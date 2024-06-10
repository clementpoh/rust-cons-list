# rust-cons-list

Implementation of an e singly linked list in Rust. It is the recursively
defined list that is introduced in [Chapter 15 of the Rust Book][book]. While
the linked list is disfavored in Rust, it's a familiar structure to many
functional programmers.

This crate extends the implementation of the basic cons list found straight in
the Rust Book to offer some conveniences similar to those implemented for the
`Vec`. Specifically, a `list!` macro for easy instantiation and implementations
of the `Display`, `Iterator`, `IntoIterator` and `FromIterator` traits.

## Definition

The type definition is lifted straight out of the Book.

``` rust
#[derive(Debug, Default, PartialEq, PartialOrd)]
pub enum List<T> {
    #[default]
    Nil,
    Cons(T, Box<List<T>>),
}
```

## Usage

### Creating a new list

A macro `list!` is defined to allow for easy instantiation.

#### Macro

``` rust
  let list = list![1, 2, 3];
  assert_eq!(list, Cons(1, Cons(2, Box::new(Cons(3, Box::new(Nil))))));
```

#### Functions

Otherwise the `cons()` and `nil()` functions are provided as an alternative.

``` rust
  let list = cons(1, cons(2, cons(3, nil)));
  assert_eq!(list, Cons(1, Cons(2, Box::new(Cons(3, Box::new(Nil))))));
```

### Manipulation

``` rust

[book]: https://doc.rust-lang.org/book/ch15-01-box.html#more-information-about-the-cons-list
