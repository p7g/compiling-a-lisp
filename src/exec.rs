use crate::object;
use memmap::Mmap;

pub(crate) struct Exec {
    mem: Mmap,
    heap: Vec<object::Uword>,
}

impl Exec {
    pub(crate) fn new(mem: Mmap) -> Self {
        Self {
            mem,
            heap: vec![0; 1024],
        }
    }

    pub(crate) fn heap(&self) -> &Vec<object::Uword> {
        &self.heap
    }

    pub(crate) fn exec(&mut self) -> u64 {
        let func: extern "C" fn(heap: *mut object::Uword) -> u64 =
            unsafe { std::mem::transmute(self.mem.as_ptr()) };
        let result = func(self.heap.as_mut_ptr());
        result
    }
}
