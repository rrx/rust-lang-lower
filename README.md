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

# Non-Goals

- Create just another "C" replacement
- Strict C interop


# Features

- [x] basic arithmetic - integer and floating point ops
- [x] global/static variables
- [x] function calling with recursion
- [x] basic C interop, with static functions
- [x] nested blocks and loops
- [x] static compilation with MLIR
- [ ] arrays
- [ ] structs, unions, and tagged unions
- [ ] module loading and import
- [ ] LSP support
- [ ] Linter support
- [ ] lambdas using CPS
- [ ] pointers
- [ ] short-circuit operators (and, or)
- [ ] flexible memory layout (C ABI, packed, struct of arrays (SOA))
- [ ] return value semantics
- [ ] type inference - Hindley-Milner
- [ ] type inference - Biunification
- [ ] lifetime inference
- [ ] heap allocation, lifetime tracing, compile time free (defer)
- [ ] byte code interpreter
- [ ] full C interop with shared libraries and headers
- [ ] integration with MUSL
- [ ] integration with SDL
- [ ] integration with GPUs
- [ ] add alternative frontends (Python, Lang3, Lisp)
- [ ] integrate with a dynamic hotreloading linker
- [ ] lower using cranelift (for faster debug builds)


