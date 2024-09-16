# Modular Compiler in Rust

This is prototype for an experimental compiler to rapidly explore programming language ideas.

Currently the frontend uses a Rust based Starlark parser, which I have extended to exercise the compiler.

# Goals

- Try something new
- Learn about compilers
- Runtime dynamic linking for full hotreloading and JIT optimizations
- Full type inteference that stays out of your way, but is useful
- Strong type system that makes refactoring easier (not heavy like Rust)
- Be flexible, allowing multiple frontends and backends
- Support LLVM only using MLIR, but not be locked in (ex: cranelift)
- Create a flexible middleware between the frontend (AST) and the backend (LLVM)
- Deep integration with OS, Database or Distributed layers
- Self compilation

# Non-Goals

- Create just another "C" replacement
- Strict C interop
- Another parser frontend
- Another low level backend (i.e. cranelift and LLVM)

# Features

- [x] basic arithmetic - integer and floating point ops
- [x] global/static variables
- [x] function calling with recursion
- [x] basic C interop, with static functions
- [x] nested blocks and loops
- [x] static compilation with MLIR
- [x] type inference - Hindley-Milner
- [ ] arrays
- [ ] structs, unions, and tagged unions
- [ ] compile time interpretation
- [ ] function polymorphism
- [ ] exhaustive case/match types
- [ ] module loading and import
- [ ] container types (sets, maps, vec, deque, queue)
- [ ] type inference - Biunification
- [ ] Linter support
- [ ] lambdas using CPS
- [ ] lifetime inference
- [ ] pointers and references
- [ ] short-circuit operators (and, or)
- [ ] flexible memory layout (C ABI, packed, struct of arrays (SOA))
- [ ] return value semantics
- [ ] LSP support
- [ ] heap allocation, lifetime tracing, compile time free (defer)
- [ ] coroutines and generators
- [ ] byte code interpreter
- [ ] full C interop with shared libraries and headers
- [ ] integration with MUSL
- [ ] integration with SDL
- [ ] integration with GPUs
- [ ] add alternative frontends (Python, Lang3, Lisp)
- [ ] compile to javascript or C
- [ ] integrate with a dynamic hotreloading linker
- [ ] lower using cranelift (for faster debug builds)

# Milestones

Working towards an MVP, which will have the following characteristics:

- executes code on a GPU and CPU 
- live hot-reload for development
- full type inference
- all front-end hacks remove, using language native constructs
- module import
- integrates with existing library code
- incremental linking and loading
- creating a simple computer game
