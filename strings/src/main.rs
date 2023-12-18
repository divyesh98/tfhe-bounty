use std::time::Instant;

use tfhe::integer::RadixCiphertext;
use tfhe::integer::ServerKey;
use tfhe::integer::RadixClientKey;
use tfhe::integer::gen_keys_radix;
use tfhe::shortint::parameters::PARAM_MESSAGE_2_CARRY_2_KS_PBS;

use rayon::prelude::*;

#[derive(Clone)]
struct FheAscii {
    block: RadixCiphertext
}

#[derive(Clone)]
struct FheString {
    blocks: Vec<FheAscii>
}

impl FheAscii {
    const NUM_BLOCKS: usize = 4;

    fn encrypt(c: &char, ck: &RadixClientKey) -> Self {
        FheAscii {
            block: ck.encrypt(*c as u8),
        }
    }

    fn decrypt(&self, ck: &RadixClientKey) -> char {
        return ck.decrypt::<u8>(&self.block) as char;
    }

    fn _get_num_blocks(&self) -> usize {
        return Self::NUM_BLOCKS;
    }
}

impl FheString {
    fn encrypt(string: &str, ck: &RadixClientKey) -> Self {
        let mut b: Vec<FheAscii> = vec![];
        for ch in string.chars() {
            b.push(FheAscii::encrypt(&ch, ck));
        }
        b.push(FheAscii::encrypt(&'\0', ck));

        FheString {
            blocks: b,
        }
    }

    fn decrypt(&self, ck: &RadixClientKey) -> String {
        let mut dec: String = String::with_capacity(0);
        for b in &self.blocks {
            let c = b.decrypt(ck);
            dec.push(c);
        }
        return dec[..dec.len()-1].to_string();
    }

    fn len(&self, sk: &ServerKey) -> RadixCiphertext {
        let mut length = sk.create_trivial_radix(0u64,FheAscii::NUM_BLOCKS);
        sk.smart_scalar_add_assign_parallelized(&mut length, (self.blocks.len()-1) as u64);

        return length;
    }

    fn is_empty(&self, sk: &ServerKey) -> RadixCiphertext {
        let mut length = self.len(sk);
        return sk.smart_scalar_eq_parallelized(&mut length, 0u64);
    }

    fn to_lower_assign_parallelized(&mut self, sk: &ServerKey) -> &Self {
        
        self.blocks.par_iter_mut().for_each(|chunk|{
            let (mut t1, mut t2) = rayon::join(
                || sk.scalar_gt_parallelized(&chunk.block, 64u64),
                || sk.scalar_lt_parallelized(&chunk.block, 91u64),
            );

            sk.smart_bitand_assign_parallelized(&mut t1, &mut t2);
            sk.smart_scalar_mul_assign_parallelized(&mut t1, 32u64);
            sk.smart_add_assign_parallelized(&mut chunk.block, &mut t1);
        });

        return self;
    }

    fn to_upper_assign_parallelized(&mut self, sk: &ServerKey) -> &Self {
        
        self.blocks.par_iter_mut().for_each(|chunk|{
            let (mut t1, mut t2) = rayon::join(
                || sk.scalar_gt_parallelized(&chunk.block, 96u64),
                || sk.scalar_lt_parallelized(&chunk.block, 123u64),
            );

            sk.smart_bitand_assign_parallelized(&mut t1, &mut t2);
            sk.smart_scalar_mul_assign_parallelized(&mut t1, 32u64);
            sk.smart_sub_assign_parallelized(&mut chunk.block,&mut t1);
        });

        return self;
    }

    fn equals(&self, cipher: &FheString, sk: &ServerKey) -> RadixCiphertext{
        let mut res = sk.create_trivial_radix(1u64, FheAscii::NUM_BLOCKS);

        let mut iter1 = self.blocks.iter();
        let mut iter2 = cipher.blocks.iter();

        loop {
            match (iter1.next(), iter2.next()) {
                (Some(item1), Some(item2)) => {
                    let mut ip1 = item1.block.clone();
                    let mut ip2 = item2.block.clone();

                    let mut temp = sk.smart_eq_parallelized(&mut ip1, &mut ip2);
                    sk.smart_mul_assign_parallelized(&mut res, &mut temp);
                }
                (None, None) => return res,
                _ => return sk.create_trivial_radix(0u64, FheAscii::NUM_BLOCKS),
            }
        }
    }

    fn equals_plain(&self, string: &str, sk: &ServerKey) -> RadixCiphertext {
        let mut res = sk.create_trivial_radix(1u64, FheAscii::NUM_BLOCKS);

        let mut iter1 = self.blocks.iter();
        let mut iter2 = string.chars();

        loop {
            match (iter1.next(), iter2.next()) {
                (Some(item1), Some(item2)) => {
                    let mut ip1 = item1.block.clone();

                    let mut temp = sk.smart_scalar_eq_parallelized(&mut ip1, item2 as u64);
                    sk.smart_mul_assign_parallelized(&mut res, &mut temp);
                }
                (None, None) => return res,
                _ => return sk.create_trivial_radix(0u64, FheAscii::NUM_BLOCKS),
            }
        }
    }

    fn not_equals(&self, cipher: &FheString, sk: &ServerKey) -> RadixCiphertext {
        let mut one = sk.create_trivial_radix(1u64, FheAscii::NUM_BLOCKS);
        let mut eq = self.equals(cipher, sk);
        return sk.smart_sub_parallelized(&mut one, &mut eq);
    }
    
    fn not_equals_plain(&self, string: &str, sk: &ServerKey) -> RadixCiphertext {
        let mut one = sk.create_trivial_radix(1u64, FheAscii::NUM_BLOCKS);
        let mut eq = self.equals_plain(string, sk);
        return sk.smart_sub_parallelized(&mut one, &mut eq);
    }

    fn concat_assign(&mut self, cipher: &FheString) -> &Self {
        self.blocks.extend(cipher.blocks.clone());
        return self;
    }

    fn starts_with(&self, cipher: &FheString, sk: &ServerKey) 
        -> RadixCiphertext {
        let mut res = sk.create_trivial_radix(1u64, FheAscii::NUM_BLOCKS);

        let mut iter1 = self.blocks.iter();
        let mut iter2 = cipher.blocks.iter().peekable();

        loop {
            if let Some(&ref current) = iter2.next() {
                if let Some(&_next) = iter2.peek() {
                
                    let mut ip1 = current.block.clone();
                    if let Some(&ref c1) = iter1.next(){

                        let mut ip2 = c1.block.clone();

                        let mut temp = sk.smart_eq_parallelized(&mut ip1, &mut ip2);
                        sk.smart_mul_assign_parallelized(&mut res, &mut temp);

                    }else{
                        return sk.create_trivial_radix(0u64, FheAscii::NUM_BLOCKS);
                    }
                }else{
                    return res;
                }
            }else {
                return sk.create_trivial_radix(0u64, FheAscii::NUM_BLOCKS);
            }
        }
    }

    fn starts_with_plain(&self, string: &str, sk: &ServerKey) 
        -> RadixCiphertext {
        let mut res = sk.create_trivial_radix(1u64, FheAscii::NUM_BLOCKS);

        let mut iter1 = self.blocks.iter();
        let mut iter2 = string.chars().peekable();

        loop {
            if let Some(current) = iter2.next() {
                if let Some(&_next) = iter2.peek() {
                
                    let ip1 = current as u64;
                    if let Some(&ref c1) = iter1.next(){

                        let mut ip2 = c1.block.clone();

                        let mut temp = sk.smart_scalar_eq_parallelized(&mut ip2, ip1);
                        sk.smart_mul_assign_parallelized(&mut res, &mut temp);

                    }else{
                        return sk.create_trivial_radix(0u64, FheAscii::NUM_BLOCKS);
                    }
                }else{
                    return res;
                }
            }else {
                return sk.create_trivial_radix(0u64, FheAscii::NUM_BLOCKS);
            }
        }
    }

    // fn eq_ignore_case(&self, cipher: &FheString, sk: &ServerKey) 
    //     -> &Self{
        
    //     let 
    // }
}

fn main(){
    let num_blocks = 4;
    let (ck, sk) = gen_keys_radix(PARAM_MESSAGE_2_CARRY_2_KS_PBS, num_blocks);
    let input = "Hi, Divyesh's Ph no: 7987267463.\0 \nRole-Researcher@TCS Research.";

    println!("Plain Input is:\n{}", input);
    println!();

    let mut now = Instant::now();
    let mut enc_ip = FheString::encrypt(&input, &ck);
    println!("Time to encrypt the input is {:?}", now.elapsed());
    println!();

    now = Instant::now();
    let dec_ip = enc_ip.decrypt(&ck);
    println!("Time to decrypt input is {:?}", now.elapsed());
    println!("Decrypted Input is\n{}", dec_ip);
    println!();

    now = Instant::now();
    let len = enc_ip.len(&sk);
    println!("length of the input string is {}, time taken={:?}", 
    ck.decrypt::<u64>(&len), now.elapsed());
    // assert_eq!(ck.decrypt::<u64>(&len) as usize, input.len());
    println!();

    now = Instant::now();
    let empty_check = enc_ip.is_empty(&sk);
    if ck.decrypt::<u64>(&empty_check) == 1 {
        println!("String is empty, time taken to check is {:?}", now.elapsed());
    }else {
        println!("String is not empoty, time taken to check is {:?}", now.elapsed());
    }
    println!();

    now = Instant::now();
    enc_ip.to_lower_assign_parallelized(&sk);
    println!("Lower case conversion of the input string is\n{}\n
    Time taken to convert to lowercase is {:?}", enc_ip.decrypt(&ck), now.elapsed());
    // assert_eq!(enc_ip.decrypt(&ck), input.to_lowercase());
    println!();
    
    now = Instant::now();
    enc_ip.to_upper_assign_parallelized(&sk);
    println!("Upper case conversion of the input string is\n{}\n
    Time taken to convert to uppercase is {:?}",enc_ip.decrypt(&ck), now.elapsed());
    // assert_eq!(enc_ip.decrypt(&ck), input.to_uppercase());
    println!();

    let string1 = "Divyesh";
    let string2 = "DivyeshS";
    let mut enc_str1 = FheString::encrypt(&string1, &ck);
    let enc_str2 = FheString::encrypt(&string2, &ck);

    now = Instant::now();
    let mut eq = enc_str1.equals(&enc_str2, &sk);
    println!("String {} and String {} encrypted equality condition is {}
    Time taken to perform equality operation is {:?}", string1, string2, 
    ck.decrypt::<u64>(&eq), now.elapsed());
    println!();

    now = Instant::now();
    eq = enc_str1.equals_plain(&string2, &sk);
    println!("String {} and String {} plain string equality condition is {}
    Time taken to perform equality operation is {:?}", string1, string2, 
    ck.decrypt::<u64>(&eq), now.elapsed());
    println!();

    now = Instant::now();
    enc_str1.concat_assign(&enc_str2);
    println!("Concatenated string is {}
    Time taken to concatenate is {:?}", enc_str1.decrypt(&ck), now.elapsed());
    println!();
    
    now = Instant::now();
    let eq = enc_str1.starts_with(&enc_str2, &sk);
    println!("Condition to check String {} starts_with String {} = {}
    Time taken to check is {:?}", enc_str1.decrypt(&ck), enc_str2.decrypt(&ck),
     ck.decrypt::<u64>(&eq), now.elapsed());
    println!();

}
