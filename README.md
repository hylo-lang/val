# Hylo (formerly Val)


[![codecov](https://codecov.io/gh/hylo-lang/hylo/graph/badge.svg?token=YF1Q8W88VN)](https://codecov.io/gh/hylo-lang/hylo)

Hylo is a programming language that leverages [mutable value semantics](Docs/ImplementationStrategiesForMutableValueSemantics.pdf) and [generic programming](https://fm2gp.com) for high-level systems programming.

This repository contains the sources of the reference implementation of Hylo.
Please visit our **[website](https://hylo-lang.org)** to get more information about the language itself.

## Developement/Use Requirements

This project is written in [Swift](https://swift.org) and distributed in the form of a package, built with [Swift Package Manager](https://swift.org/package-manager/).
You will need Swift 5.10 or higher to build the compiler from sources.

**This repository contains
[submodules](https://git-scm.com/book/en/v2/Git-Tools-Submodules)**,
so after cloning, issue `git submodule update --init` to populate
them.

**Windows users:** this repository contains symbolic links, so you'll
need to [enable support](https://stackoverflow.com/a/59761201/125349)
for them before checking it out.

### LLVM

This package requires LLVM 17.  Major versions of LLVM are not
interchangeable or backward-compatible.

If you are using this package for development we strongly recommend
the use of an LLVM with assertions enabled such as
[these](https://github.com/hylo-lang/llvm-build); otherwise it's much
too easy to violate LLVM's preconditions without knowing it.  This
package's devcontainer (in the `.devcontainer` subdirectory) has an
assert-enabled LLVM build preinstalled in
`/opt/llvm-MinSizeRel`. Instructions to install a debug build are in a
comment in `.devcontainer/Dockerfile`.

*If* you want to build with the Swift Package Manager and you choose
to get LLVM some other way, you'll need an installation with an
`llvm-config` executable, which we will use to create a `pkg-config`
file for LLVM.

## Building with CMake and Ninja

1. **Configure**: choose a *build-directory* and a CMake *build type*
   (usually `Debug` or `Release`) and then, where `<LLVM>` is the path
   to the root directory of your LLVM installation,

	```
	cmake -D CMAKE_BUILD_TYPE=<build-type> \
	  -D LLVM_DIR=<LLVM>/lib/cmake/llvm   \
      -G Ninja -S . -B <build-directory>
    ```

    (on Windows substitute your shell's line continuation character
    for `\` or just remove the line breaks and backslashes).
    
    If you want to run tests, add `-DBUILD_TESTING=1`.
    
    **Note:** on macOS, if you are not using your Xcode's default
    toolchain, [you may need `-D
    CMAKE_Swift_COMPILER=swiftc`](https://gitlab.kitware.com/cmake/cmake/-/issues/25750)
    to prevent CMake from using Xcode's default `swift`.
    
    If this command fails it could be because you have an LLVM without
    CMake support installed; we suggest you try one of
    [these](https://github.com/hylo-lang/llvm-build) packages instead.

2.  **Build**: 

    ```
    cmake --build <build-directory>
    ```

3. **Test** (requires `-DBUILD_TESTING=1` in step 1):

   ```
   ctest --parallel --test-dir <build-directory>
   ```

## Building with CMake and Xcode

You will need CMake 3.3.0-rc1 or newer.

1. **Generate Xcode project**: choose a *build-directory* and then,
   where `<LLVM>` is the path to the root directory of your LLVM
   installation,

    ```
    cmake -D LLVM_DIR=<LLVM>/lib/cmake/llvm \
      -G Xcode -S . -B <build-directory>
    ```

    If you want to run tests, add `-DBUILD_TESTING=1`.

2. **Profit**: open the `.xcodeproj` file in the *build-directory* and
   use Xcode's UI to build and test.

## Building with Swift Package Manager

**Windows Users:** Swift Package Manager is poorly supported on
Windows and we've been seeing a number of tests act flaky on Windows
only when run under Swift Package Manager.  We strongly recommend
[using CMake](#building-with-cmake-and-ninja) instead.

**Everyone:** Swift Package Manager is poorly supported in general and
we're considering dropping our use of it, so think about [using CMake
with ninja](#building-with-cmake-and-ninja) or [with
Xcode](#building-with-cmake-and-xcode) instead.

First, you need to create a `pkgconfig` file specific to your
installation and make it visible to your build tools.  We use a `bash`
script as follows in the top-level directory of this project:

```bash
./Tools/make-pkgconfig.sh ./llvm.pc
``` 

if you are on Windows, your `git` installation (which is required for
Swift) contains a `bash` executable so you can do something like:

```bash
C:\Program Files\Git\bin\bash ./Tools/make-pkgconfig.sh ./llvm.pc
``` 

The command above generates `llvm.pc` in the current directory and
prints its contents to the terminal.  You can either add its directory
to your `PKG_CONFIG_PATH` environment variable for use with
command-line tools:

```bash
export PKG_CONFIG_PATH=$PWD
```

or you can put it somewhere that `pkg_config` already searches (needed
for use with Xcode):

```bash
sudo mkdir -p /usr/local/lib/pkgconfig && sudo mv llvm.pc /usr/local/lib/pkgconfig/
```

Once `llvm.pc` is set up, you should be able to **build this project**
using Swift package manager:

```bash
swift build -c release
```

That command will create an executable named `hc` in `.build/release`.
That's Hylo's compiler!

To test your compiler,

```bash
swift test -c release --parallel
```

#### Notes to macOS users:

1. Add `platforms: [.macOS("xxx")]` to `Package.swift` where `xxx` is
   your macOS version to address the warning complaining that an
   "object file was built for newer macOS version than being linked".
2. You may need to add the path to `zstd` library in `llvm.pc`.

### Building a Hylo Devcontainer with VSCode

While Hylo supports Linux natively, it also provides a [Devcontainer](https://containers.dev/) specification to develop for Linux on other platforms through a Docker container. Our [Linux CI](.github/workflows/build-and-test.yml) uses this specification; this makes it possible to run Linux CI locally on other operating systems like macOS. While this specification should work for any IDE that supports devcontainers, keep in mind this team only uses VSCode.

When opening the Hylo project in VSCode for the first time, you should be prompted to install the extension `recommendations` in `.vscode/extensions.json`. If you are not prompted, manually install the extensions by searching for the extension identifiers in the Extensions Marketplace.

Then, build the Devcontainer with the VSCode command: `> Dev Containers: Rebuild and Reopen in Container`.

Finally, open a new integrated terminal in VSCode and confirm that the shell user is `vscode`. You can run `whoami` to check this.

That integrated terminal is connected to the Devcontainer, as if by ssh.  
You can now follow the instructions for Building and testing [with CMake and Ninja](#building_with_ cmake_and_ninja) or [with Swift Package Manager](#building_with_swift_package_manager).
All prerequisites, including the `llvm.pc` file in the default `PKG_CONFIG_PATH`, are preinstalled.

The Hylo repository files are mounted into the container, so any changes made locally (in VSCode or in other editors) will be automatically propagated into the Devcontainer. However, if you need to modify any of the files in the `.devcontainer` directory, you will need to rebuild the container with `> Dev Containers: Rebuild and Reopen in Container`.

### Submitting issues

For submitting issue reports you need to manually update the Hylo version.
Without this step, ``hc --version`` returns ``unknown``.

```bash
./Tools/set-hc-version.sh
```

## Implementation status

This project is under active development; expect things to break and APIs to change.

The compiler pipeline is organized as below.
You can select how deep the compiler should go through the pipeline with the following options:
- `--emit raw-ast`: Only parse the input files and output an untyped AST as a JSON file.
- `--typecheck`: Run the type checker on the input.
- `--emit raw-ir`: Lower the typed AST into Hylo IR and output the result in a file.
- `--emit ir`: Run mandatory IR passes and output the result in a file.
- `--emit llvm`: Transpile the program to LLVM and output LLVM IR.
- `--emit intel-asm`: Output Intel assembly for all user module(s).
- `--emit binary` (default): Produce an executable.

For example, `hc --emit raw-ast -o main.json main.hylo` will parse `main.hylo`, write the untyped AST in `main.json`, and exit the pipeline.

A more detailed description of the current implementation status is available on our [roadmap page](https://www.hylo-lang.org/pages/implementation-status.html).

## Contributing

We welcome contributions to Hylo.
Please read through [CONTRIBUTING.md](CONTRIBUTING.md) for details on how to get started.

You can also get in touch with the community by joining our [Slack][join-slack] or one of our [Zoom Meetings][join-zoom]
(ID: 633 2146 3694, Passcode: 409180) on Tuesdays and Thursdays, 13:00-13:30 Pacific time or 22:00-22:30 Central
European time.

[join-slack]: https://join.slack.com/t/val-qs97696/shared_invite/zt-1z3dsblrq-y4qXfEE6wr6uMEJSN9uFyg
[join-zoom]: https://unige.zoom.us/j/63321463694?pwd=L0VuY3QwUEx5K3BaRWIyMjArdkhEQT09

## License

Hylo is distributed under the terms of the Apache-2.0 license.
See [LICENSE](LICENSE) for details.
