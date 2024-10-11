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

macro_rules! byte_slice_ptr {
    ($t:ty, $item:expr) => {
        unsafe { core::ptr::slice_from_raw_parts($item as *const $t as *const u8, size_of::<$t>()) }
    };
}

pub(crate) use byte_slice;
pub(crate) use byte_slice_ptr;
pub(crate) use debugprint;
