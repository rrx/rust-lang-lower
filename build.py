import os
import sys
import glob

compiler_debug = "target/x86_64-unknown-linux-gnu/debug/parse"
compiler_release = "target/x86_64-unknown-linux-gnu/release/parse"

def generate_inputs(fp, interp=True, graphs=True):
    input_directory = "tests/bin"

    def gen_with_rule(kind, compiler, defaults=False):
        outputs = []
        images = []
        for f in glob.glob(os.path.join(input_directory, "*.star")):
            target = os.path.join("build", "tests", kind, "bin")
            directory, filename = os.path.split(f)
            base, ext = os.path.splitext(filename)
            input_filename = os.path.join(input_directory, filename)

            mlir_filename = os.path.join(target, f"{base}.mlir")
            interp_filename = os.path.join(target, f"{base}.interp.out")
            blocks_input_filename = os.path.join(target, f"{base}.blocks.dot")
            blocks_output_filename = os.path.join(target, f"{base}.blocks.png")
            scopes_input_filename = os.path.join(target, f"{base}.scopes.dot")
            scopes_output_filename = os.path.join(target, f"{base}.scopes.png")
            graph_input_filename = os.path.join(target, f"{base}.graph.dot")
            graph_output_filename = os.path.join(target, f"{base}.graph.png")
            cfg_input_filename = os.path.join(target, f"{base}.cfg.mmd")
            cfg_output_filename = os.path.join(target, f"{base}.cfg.png")
            fp.write(f"build {mlir_filename} | {graph_input_filename} {blocks_input_filename} {scopes_input_filename} {cfg_input_filename}: mlir-{kind} {input_filename} | {compiler}\n")

            if interp:
                fp.write(f"build {interp_filename}: interpret-{kind} {input_filename} | {compiler}\n")

            graph_targets = []
            if graphs:
                graph_targets.append(graph_output_filename)
                fp.write(f"build {graph_output_filename}: dot-png {graph_input_filename}\n")
                graph_targets.append(blocks_output_filename)
                fp.write(f"build {blocks_output_filename}: dot-png {blocks_input_filename}\n")
                graph_targets.append(scopes_output_filename)
                fp.write(f"build {scopes_output_filename}: dot-png {scopes_input_filename}\n")
                graph_targets.append(cfg_output_filename)
                fp.write(f"build {cfg_output_filename}: mermaid-png {cfg_input_filename}\n")

            llvm_filename = os.path.join(target, f"{base}.llvm")
            fp.write(f"build {llvm_filename}: mlir-opt {mlir_filename}\n")

            object_filename = os.path.join(target, f"{base}.o")
            fp.write(f"build {object_filename}: llvm-compile {llvm_filename}\n")

            exe_filename = os.path.join(target, f"{base}")
            fp.write(f"build {exe_filename}: link-{kind} {object_filename}\n")

            run_filename = os.path.join(target, f"{base}.out")
            fp.write(f"build {run_filename}: run {exe_filename}\n")

            top = f"{base}-{kind}-exe"
            fp.write(f"build {top}: phony {run_filename} {' '.join(graph_targets)}\n")
            outputs.append(top)

            top = f"{base}-{kind}-interp"
            fp.write(f"build {top}: phony {interp_filename}\n")
            outputs.append(top)

            if defaults:
                fp.write(f"build {base}: phony {base}-{kind}-exe | {compiler}\n")

        fp.write(f"build testbins-{kind}: phony | {compiler} {' '.join(outputs)}\n")


    gen_with_rule("debug", compiler_debug, defaults=True)
    gen_with_rule("release", compiler_release)

    fp.write("default prelude-debug testbins-debug\n")
    fp.write("build all: phony testbins-debug testbins-release\n")


def main():
    build_filename = "build.ninja"

    with open(build_filename, "w") as fp:
        fp.write(
            f"""
rule compiler-release
    command = cargo build --release

rule compiler-debug
    command = cargo build

rule mlir-debug
    command = cargo run -- -v -o $out -i $in

rule mlir-release
    command = cargo run --release -- -v -o $out -i $in

rule interpret-debug
    command = cargo run -- --interp -v -i $in -o $out

rule interpret-release
    command = cargo run --release -- --interp -v -i $in -o $out

rule mlir-opt
    command = mlir-opt \
		--mem2reg \
		--sccp \
		--enable-gvn-hoist \
		--enable-gvn-sink \
		--test-lower-to-llvm \
		$in | mlir-translate -mlir-to-llvmir -o $out

rule clang-compile-debug
    command = clang -g -c $in -o $out

rule clang-compile-release
    command = clang -c $in -o $out

rule clang-shared-debug
    command = clang -shared $in -o $out

rule clang-shared-release
    command = clang -g -shared $in -o $out

rule llvm-compile
    command = clang -x ir -c -o $out $in

rule link-debug
    command = clang -o $out $in target/debug/prelude.o

rule link-release
    command = clang -o $out $in target/release/prelude.o

rule dot-png
    command = dot $in -Tpng -o $out

rule mermaid-png
    command = mmdc -o $out -i $in

rule run
    command = $in > $out

build {compiler_release}: compiler-release prelude-release
build {compiler_debug}: compiler-debug prelude-debug

build target/debug/prelude.o: clang-compile-debug tests/prelude.c
build target/debug/prelude.so: clang-shared-debug tests/prelude.c
build target/release/prelude.o: clang-compile-release tests/prelude.c
build target/release/prelude.so: clang-shared-release tests/prelude.c
build prelude-debug: phony target/debug/prelude.o target/debug/prelude.so
build prelude-release: phony target/release/prelude.o target/release/prelude.so
"""
        )
        generate_inputs(fp)
    print("Wrote", build_filename)

if __name__ == '__main__':
    main()
