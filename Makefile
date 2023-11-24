default: run

run:
	clang-17 -c tests/prelude.c -o target/debug/prelude.o
	cargo run --bin cli
	mlir-opt-17 \
		--mem2reg \
		--sccp \
		--enable-gvn-hoist \
		--enable-gvn-sink \
		--test-lower-to-llvm \
		out.ll | mlir-translate-17 -mlir-to-llvmir -o target/debug/out.llvm 
	clang-17 -x ir -c -o target/debug/out.o target/debug/out.llvm
	clang-17 -o out target/debug/out.o target/debug/prelude.o

	#mlir-opt-17 out.ll | mlir-translate-17 -mlir-to-llvmir | clang-17 -x ir -o out -
	#mlir-opt-17 out.ll | mlir-translate-17 -mlir-to-llvmir
	#mlir-translate-17 --mlir-to-llvmir out.ll | clang-17 -x ir -o out - 
	#mlir-opt-17 \
		#-test-print-defuse \
		#out.ll
	./out ; echo $$?

test:
	cargo test -- --nocapture
fmt:
	cargo fmt
