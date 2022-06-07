use bft_types::BFProgram;
use std::path::Path;

pub struct VM<T> {
    num_cells: usize,
    tape: Vec<T>,
    can_grow: bool,
}

impl<T> VM<T> {
    pub fn new(size: usize, can_grow: bool) -> Self {
        let mut num_cells = 30000;
        if size != 0 {
            num_cells = size;
        };
        let tape = Vec::with_capacity(num_cells);
        Self {
            num_cells,
            tape,
            can_grow,
        }
    }

    pub fn interpret<P: AsRef<Path>>(self, prog: &BFProgram<P>) {
        // "instructions" are private data, needed a getter method
        for i in prog.instructions() {
            println!("{}", i);
        }
    }
}

#[cfg(test)]

mod tests {

    use crate::BFProgram;
    use crate::VM;

    #[test]
    fn test_interpret() {
        // Not really a test. Just for debugging.
        // Need `-- --nocapture` to view output
        let prog = BFProgram::new("TestFile", "<>.hello.".to_string());
        let vm: VM<usize> = VM::new(0, false);
        vm.interpret(&prog);
    }
}
