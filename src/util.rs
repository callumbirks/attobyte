#[allow(unused_macros)]
macro_rules! debugprint {
    ($($arg:tt)*) => {
        #[cfg(test)]
        {
            println!($($arg)*);
        }
    };
}

macro_rules! byte_slice {
    ($t:ty, $item:expr) => {
        unsafe { core::slice::from_raw_parts($item as *const $t as *const u8, size_of::<$t>()) }
    };
}

pub(crate) use byte_slice;
#[allow(unused_imports)]
pub(crate) use debugprint;
