#![feature(is_some_and)]

mod runtime;

use std::{ops::Deref, time::Duration};

use runtime::Template;

use crate::runtime::{App, Atom, Machine};

fn main() {
    let prog = last_or(vec![1, 2, 3, 4, 5, 6, 7, 8, 9], 420);
    let mut machine = Machine::new(prog);
    let res = machine.run();
    println!("{res}");
}

fn simple() -> Vec<Template> {
    use Atom::*;
    vec![template!(
        0,
        [Ptr(1), Ptr(2)],
        [[Int(5), Prim("-")], [Int(2), Ptr(0)], [Ptr(1), Prim("+")]]
    )]
}

fn triangle_number(n: isize) -> Vec<Template> {
    use Atom::*;
    vec![
        template!(0, [Fun!(1 1), Int(n)], []),
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
    ]
}

fn head_or(v: Vec<isize>, other: isize) -> Vec<Template> {
    let mut list = vec![];
    for (i, val) in v.iter().rev().skip(1).rev().enumerate() {
        list.push(App(vec![Con!(2 1), Int(*val), Ptr(i + 1)]))
    }
    if let Some(last) = v.last() {
        list.push(App(vec![Con!(2 1), Int(*last), Con!(0 0)]))
    } else {
        list.push(App(vec![Con!(0 0)]))
    }
    use Atom::*;
    vec![
        Template {
            arity: 0,
            spine: App(vec![Fun!(2 1), Int(other), Ptr(0)]),
            apps: list,
        },
        template!(2, [Arg(1), Table(2), Arg(0)], []),
        template!(2, [Arg(1)], []),
        template!(4, [Arg(0)], []),
    ]
}

fn last_or(v: Vec<isize>, other: isize) -> Vec<Template> {
    let mut list = vec![];
    for (i, val) in v.iter().rev().skip(1).rev().enumerate() {
        list.push(App(vec![Con!(2 1), Int(*val), Ptr(i + 1)]))
    }
    if let Some(last) = v.last() {
        list.push(App(vec![Con!(2 1), Int(*last), Con!(0 0)]))
    } else {
        list.push(App(vec![Con!(0 0)]))
    }
    use Atom::*;
    vec![
        Template {
            arity: 0,
            spine: App(vec![Fun!(2 1), Int(other), Ptr(0)]),
            apps: list,
        },
        template!(2, [Arg(1), Table(2), Arg(0)], []), // a xs -> xs(TAB2) a
        template!(2, [Arg(1)], []),                   // t a -> return a
        template!(4, [Arg(1), Table(4), Arg(0), Arg(3)], []), // x xs t a -> xs(TAB4) x a
        template!(3, [Arg(1)], []),                   // t x a -> return x
        template!(5, [Fun!(4 3), Arg(0), Arg(1), Int(69), Arg(4)], []), // x' xs' t x a -> FUN4 x' xs' 69 a
    ]
}
