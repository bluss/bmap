use arrayvec::ArrayVec;

type Entries = ArrayVec<[Entry; 6]>;

const ORDER: usize = 7;

struct Entry {
    keys: ArrayVec<[u8; ORDER - 1]>,
    children: ArrayVec<[Box<Entry>; ORDER]>,
}

pub struct Bplus {
    length: usize,
    root: Entry,
}

impl Entry {
    pub fn new() -> Self {
        Entry {
            keys: ArrayVec::new(),
            children: ArrayVec::new(),
        }
    }
}

impl Bplus {
    pub fn new() -> Self {
        Bplus {
            length: 0,
            root: Entry::new(),
        }
    }
}


#[test]
fn test_new() {
    let mut bp = Bplus::new();
}

