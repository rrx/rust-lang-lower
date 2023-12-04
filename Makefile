default: run

run:
	clang-17 -c tests/prelude.c -o target/debug/prelude.o
	RUST_BACKTRACE=1 cargo run --bin cli -- -l -v -x \
		       -o target/debug/out.mlir \
		       tests/test_global.star
	mlir-opt-17 \
		--mem2reg \
		--sccp \
		--enable-gvn-hoist \
		--enable-gvn-sink \
		--test-lower-to-llvm \
		target/debug/out.mlir | mlir-translate-17 -mlir-to-llvmir -o target/debug/out.llvm 
	clang-17 -x ir -c -o target/debug/out.o target/debug/out.llvm
	clang-17 -o target/debug/out target/debug/out.o target/debug/prelude.o

	#mlir-opt-17 out.ll | mlir-translate-17 -mlir-to-llvmir | clang-17 -x ir -o out -
	#mlir-opt-17 out.ll | mlir-translate-17 -mlir-to-llvmir
	#mlir-translate-17 --mlir-to-llvmir out.ll | clang-17 -x ir -o out - 
	#mlir-opt-17 \
		#-test-print-defuse \
		#out.ll
	./target/debug/out ; echo $$?

test:
	cargo test -- --nocapture
fmt:
	cargo fmt

.PHONY: examples
examples:
	clang-17 -c examples/test.c -o target/debug/test.o
	clang-17 -S -emit-llvm examples/test.c -o target/debug/test.ll
	cat target/debug/test.ll
