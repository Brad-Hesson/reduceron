#![feature(is_some_and)]
use std::{ops::Deref, time::Duration};

macro_rules! template {
    ($arity:expr, $spine:tt, [$($app:tt),*]) => {
        Template{
            arity: $arity,
            spine: template!($spine),
            apps: vec![$(template!($app)),*]
        }
    };
    ([$($atom:expr),*]) => {
        App(vec![$($atom),*])
    };
}

macro_rules! Fun {
    ($a:tt $b:tt) => {
        Atom::Fun {
            arity: $a,
            addr: $b,
        }
    };
}
macro_rules! Con {
    ($a:tt $b:tt) => {
        Atom::Con {
            tab_loc: $a,
            ind: $b,
        }
    };
}

fn main() {
    use Atom::*;
    let prog_simp = template!(
        0,
        [Ptr(1), Ptr(2)],
        [[Int(5), Prim("-")], [Int(2), Ptr(0)], [Ptr(1), Prim("+")]]
    );
    let prog_tri = vec![
        template!(0, [Fun!(1 1), Int(5)], []),
        template!(
            1,
            [Int(1), Ptr(0), Table(2), Arg(0)],
            [[Arg(0), Prim("<=")]]
        ),
        template!(
            2,
            [Arg(1), Ptr(0)],
            [
                [Fun!(1 1), Ptr(1), Prim("+")],
                [Int(1), Ptr(2)],
                [Arg(1), Prim("-")]
            ]
        ),
        template!(2, [Int(1)], []),
    ];
    let prog_head_or = vec![
        template!(
            0,
            [Fun!(2 1), Int(9), Ptr(0)],
            [[Con!(0 0)]] // [[Con!(2 1), Int(1), Ptr(1)], [Con!(2 1), Int(2), Con!(0 0)]]
        ),
        template!(2, [Arg(1), Table(2), Arg(0)], []),
        template!(2, [Arg(1)], []),
        template!(4, [Arg(0)], []),
    ];
    let last_or = vec![
        template!(
            0,
            [Fun!(2 1), Int(420), Ptr(0)],
            // [[Con!(0 0)]]
            [[Con!(2 1), Int(1), Ptr(1)], [Con!(2 1), Int(2), Ptr(2)], [Con!(2 1), Int(3), Con!(0 0)]]
        ),
        template!(2, [Arg(1), Table(2), Arg(0)], []), // a xs -> xs(TAB2) a
        template!(2, [Arg(1)], []), // t a -> return a
        template!(4, [Arg(1), Table(4), Arg(0), Arg(3)], []), // x xs t a -> xs(TAB4) x a
        template!(3, [Arg(1)], []), // t x a -> return x
        template!(5, [Fun!(4 3), Arg(0), Arg(1), Int(69), Arg(4)], []), // x' xs' t x a -> FUN4 x' xs' 69 a
    ];
    let mut machine = Machine::new(last_or);
    let res = machine.run();
    println!("{res}");
}

#[derive(Debug, Clone)]
enum Atom {
    Fun { arity: usize, addr: usize },
    Arg(usize),
    Ptr(usize),
    Con { tab_loc: usize, ind: usize },
    Int(isize),
    Prim(&'static str),
    Table(usize),
}
impl Atom {
    fn arity(&self) -> Option<usize> {
        match self {
            Atom::Fun { arity, .. } => Some(*arity),
            Atom::Con { tab_loc: arity, .. } => Some(*arity + 1),
            Atom::Int(_) => Some(1),
            Atom::Prim(_) => Some(2),
            _ => unreachable!(),
        }
    }
}

#[derive(Debug, Clone)]
struct Template {
    arity: usize,
    spine: App,
    apps: Vec<App>,
}

#[derive(Debug, Clone)]
struct App(Vec<Atom>);
impl App {
    fn instantiate(&mut self, machine: &Machine) {
        let base = machine.heap.len();
        for a in &mut self.0 {
            if let Atom::Ptr(addr) = a {
                *a = Atom::Ptr(*addr + base)
            }
            if let Atom::Arg(ind) = a {
                let len = machine.stack.len() - 1;
                *a = machine.stack[len - *ind].clone();
            }
        }
    }
}

#[derive(Debug)]
struct Update {
    stack_addr: usize,
    heap_addr: usize,
}

struct Machine {
    program: Vec<Template>,
    heap: Vec<App>,
    stack: Vec<Atom>,
    ustack: Vec<Update>,
}
impl Machine {
    fn new(program: Vec<Template>) -> Self {
        Self {
            program,
            heap: vec![],
            stack: vec![Atom::Fun { arity: 0, addr: 0 }],
            ustack: vec![],
        }
    }
    fn step(&mut self) {
        //  step (p, h, PTR x:s, u) = (p, h, h!!x ++ s, upd:u)
        //      where upd = (1+length s, x)
        if matches!(self.stack[..], [.., Atom::Ptr { .. }]) {
            // println!("Unwinding");
            let Atom::Ptr(addr) = self.stack.pop().unwrap() else {unreachable!()};
            self.ustack.push(Update {
                stack_addr: self.stack.len() + 1,
                heap_addr: addr,
            });
            self.stack.extend(self.heap[addr].0.iter().cloned().rev());
            return;
        }
        //  step (p, h, top:s, (sa,ha):u)
        //      | arity top > n = (p, h’, top:s, u)
        //      where
        //          n = 1+length s - sa
        //          h’ = update ha (top:take n s) h
        if matches!(
            (&self.stack[..], &self.ustack[..]),
            ([..,s], [..,Update { stack_addr, .. }])
            if s.arity().is_some_and(|a| a + *stack_addr > self.stack.len())
        ) {
            // println!("Updating");
            let Update {
                stack_addr,
                heap_addr,
            } = self.ustack.pop().unwrap();
            self.heap[heap_addr] = App(self
                .stack
                .iter()
                .rev()
                .take(self.stack.len() + 1 - stack_addr)
                .cloned()
                .collect());
            return;
        }
        //  step (p, h, INT n:x:s, u) = (p, h, x:INT n:s, u)
        if matches!(&self.stack[..], [.., _, Atom::Int(_)]) {
            // println!("Integer swap");
            let last = self.stack.len() - 1;
            self.stack.swap(last, last - 1);
            return;
        }
        //  step (p, h, PRI f:x:y:s, u) = (p, h, prim f x y:s, u)
        if matches!(
            &self.stack[..],
            [.., Atom::Int(_), Atom::Int(_), Atom::Prim(_)]
        ) {
            // println!("Primitive application");
            let Atom::Prim(f) = self.stack.pop().unwrap() else {unreachable!()};
            let Atom::Int(a) = self.stack.pop().unwrap() else {unreachable!()};
            let Atom::Int(b) = self.stack.pop().unwrap() else {unreachable!()};
            self.stack.push(prim(f, a, b));
            return;
        }
        //  step (p, h, CON n j:s, u) = (p, h, FUN 0 (i+j):s,u)
        //      where TAB i = s!!n
        if matches!(&self.stack[..], [.., Atom::Con { .. }]) {
            // println!("Constructors");
            let Atom::Con { tab_loc: arity, ind } = self.stack.pop().unwrap() else {unreachable!()};
            let last = self.stack.len() - 1;
            let Atom::Table(i) = self.stack[last - arity] else {unreachable!()};
            self.stack.push(Atom::Fun {
                arity: 0,
                addr: i + ind,
            });
            return;
        }
        if matches!(&self.stack[..], [.., Atom::Fun { .. }]) {
            // println!("Function application");
            let Atom::Fun { addr: f, .. } = self.stack.pop().unwrap() else {unreachable!()};
            let Template {
                arity,
                mut spine,
                mut apps,
            } = self.program[f].clone();
            spine.instantiate(self);
            apps.iter_mut().for_each(|app| app.instantiate(self));
            self.heap.extend(apps);
            self.stack.truncate(self.stack.len() - arity);
            self.stack.extend(spine.0.into_iter().rev());
            return;
        }
        unreachable!()
    }
    fn run(&mut self) -> isize {
        for n in 1.. {
            self.step();
            self.dump();
            if let [Atom::Int(i)] = &self.stack[..] {
                println!("Took {n} iterations");
                return *i;
            }
            // std::thread::sleep(Duration::from_secs(1));
        }
        unreachable!()
    }
    fn dump(&self) {
        println!("-----STACK-----");
        for a in self.stack.iter().rev() {
            println!("{a:?}")
        }
        println!("-----HEAP-----");
        for a in &self.heap {
            println!("{a:?}")
        }
        println!("-----USTACK-----");
        for a in &self.ustack {
            println!("{a:?}")
        }
        println!();
    }
}

fn prim(f: &str, a: isize, b: isize) -> Atom {
    match f {
        "+" => Atom::Int(a + b),
        "-" => Atom::Int(a - b),
        "<=" => bool_con(a <= b),
        "==" => bool_con(a == b),
        _ => unimplemented!(),
    }
}
fn bool_con(b: bool) -> Atom {
    match b {
        false => Atom::Con { tab_loc: 0, ind: 0 },
        true => Atom::Con { tab_loc: 0, ind: 1 },
    }
}
