# Troubleshooting compiler build issues

## Some of my CI builds succeed, and some fail.

At this point, Hylo compiler uses both a build system based on CMake, and one based on `swift build`.
Investigate if just one of them fails, and take it from there.

## Updating an external library

Let's take the example of Swifty-LLVM, which is a Hylo repository for which we always get the latest version from `main`.
For this example, making a change to Swifty-LLVM should be picked up automatically by the CMake build, after the change is submitted to `main`.
But this doesn't happen with the native swift build system.

To properly update the external library, do the following:
- quit any IDEs (yes, please do that)
- delete the build folder (e.g., `.build`)
- delete `Package.resolved`
- build with Swift build system (e.g., `swift build -c release`), and ensure everything builds
- build with the CMake system and ensure that everything builds
- upload the changes to `Package.resolved`; this should contain the commit sha for the latest version of the library.

> **_NOTE:_**
> VS Code imediatelly re-generates the swift packages, so, depending on the order of operations, this may interfere with the actual resolving of the packages.
> This is why we recommend closing the IDE first.

> **_NOTE:_**
> This will most probably update other packages that swift will use (unrelated content in `Package.resolved` is changed).
> This is expected.