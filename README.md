# Compiling a Lisp

In this repo I'm following along with [this][1] series of blog posts to write a
Lisp to x86-64 machine code. I decided to adapt it to Rust since I haven't
written any in a while.

[1]: https://bernsteinbear.com/blog/compiling-a-lisp-0/

For the most part, I shouldn't deviate from the posts too much, but in some
cases it makes sense to, e.g. using an enum to represent AST nodes instead of
pointer tagging.
