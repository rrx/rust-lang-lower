default: run

run:
	cargo run --bin lower
	#mlir-opt-17 --test-lower-to-llvm out.ll | mlir-translate-17 -mlir-to-llvmir | clang-17 -x ir -o out -
	#mlir-opt-17 out.ll | mlir-translate-17 -mlir-to-llvmir | clang-17 -x ir -o out -
	#mlir-opt-17 out.ll | mlir-translate-17 -mlir-to-llvmir
	mlir-translate-17 -mlir-to-llvmir out.ll | clang-17 -x ir -o out - 
	./out ; echo $$?

