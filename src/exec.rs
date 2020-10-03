use memmap::Mmap;

pub(crate) struct Exec(Mmap);

impl Exec {
    pub(crate) fn new(mem: Mmap) -> Self {
        Self(mem)
    }

    pub(crate) fn exec(&self) -> i32 {
        let func: extern "C" fn() -> i32 = unsafe {
            std::mem::transmute(self.0.as_ptr())
        };
        func()
    }
}
