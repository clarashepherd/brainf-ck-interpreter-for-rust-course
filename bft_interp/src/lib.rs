use bft_types::BFProgram;

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
}

#[cfg(test)]
mod tests {}
