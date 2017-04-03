use eval_context::{EvalContext};

pub struct Executor<'a, 'tcx: 'a> {
    queue: Vec<EvalContext<'a, 'tcx>>,
}

impl <'a, 'tcx: 'a>  Executor<'a, 'tcx> {
    pub fn new() -> Self {
        Executor {
            queue: Vec::new(),
        }
    }
}
