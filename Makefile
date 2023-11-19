default: run

run:
	cargo run --bin lower
	mlir-opt-17 --test-lower-to-llvm out.mlir | mlir-translate-17 -mlir-to-llvmir | clang-17 -x ir -o out -
	./out ; echo $$?

