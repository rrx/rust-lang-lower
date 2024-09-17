export RUST_BACKTRACE=1
default: ninja

ninja:
	cargo check
	cargo build
	python3 build.py
	#touch target/x86_64-unknown-linux-gnu/debug/parse
	ninja
	@echo COMPLETE

clean:
	cargo clean
	rm -rf build

bare:
	RUST_BACKTRACE=1 cargo run -- -x -v -i tests/bin/bare.star

template:
	RUST_BACKTRACE=1 cargo run -- -t -v -i tests/template.star

t:
	RUST_BACKTRACE=1 cargo run -- -x -v -i tests/bin/star_args.star -o build/args3

run:
	cargo check
	python3 build.py
	touch target/x86_64-unknown-linux-gnu/debug/parse
	ninja -v test_ternary

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

fmt:
	cargo fmt

.PHONY: examples
examples:
	clang-17 -c tests/prelude.c -o target/debug/prelude.o
	clang-17 -shared tests/prelude.c -o target/debug/prelude.so
	clang-17 -c examples/test.c -o target/debug/test.o
	clang-17 -S -emit-llvm examples/test.c -o target/debug/test.ll
	cat target/debug/test.ll
