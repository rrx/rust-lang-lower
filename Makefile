default: run

seq:
	RUST_BACKTRACE=1 RUST_LOG=debug cargo test -- --nocapture test_seq3
	make graphs

bare:
	RUST_BACKTRACE=1 cargo run --example flatten -- -x -v tests/test_recursive.star

run:
	#RUST_BACKTRACE=1 cargo run --example flatten -- -x -v tests/test_cond.star
	#RUST_BACKTRACE=1 cargo run --example flatten -- -x -v tests/static_var.star
	RUST_BACKTRACE=1 cargo run --example flatten -- -x -v tests/nested_func.star
	#RUST_BACKTRACE=1 cargo run --example flatten -- -x -v tests/test.star || true
	#RUST_BACKTRACE=1 cargo run --example flatten -- -x -v tests/goto.star
	#RUST_BACKTRACE=1 cargo run --example flatten -- -x -v tests/goto.star || true
	dot out.dot -Tpng -o out.png
	dot blocks.dot -Tpng -o blocks.png
	dot scopes.dot -Tpng -o scopes.png

	#RUST_BACKTRACE=1 cargo run --example flatten -- -x -v tests/test_cond.star

graphs:
	dot out.dot -Tpng -o out.png
	dot flat/blocks.dot -Tpng -o blocks.png
	dot scopes.dot -Tpng -o scopes.png


run0:
	RUST_BACKTRACE=1 cargo run --bin parse -- -v tests/goto.star

run_test:
	RUST_BACKTRACE=1 cargo run --bin parse -- -l -v -x \
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

test: examples
	cargo test -j1 -- --nocapture
fmt:
	cargo fmt

.PHONY: examples
examples:
	clang-17 -c tests/prelude.c -o target/debug/prelude.o
	clang-17 -shared tests/prelude.c -o target/debug/prelude.so
	clang-17 -c examples/test.c -o target/debug/test.o
	clang-17 -S -emit-llvm examples/test.c -o target/debug/test.ll
	cat target/debug/test.ll
