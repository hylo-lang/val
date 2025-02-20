# HOWTOs

## Updating an external library

We use Swifty-LLVM as an example of external library that needs to be updated.
We assume that there is a change on the `main` branch of Swifty-LLVM that should be used by Hylo compiler.

Steps:
- In [`CMakeModules` repository](https://github.com/hylo-lang/CMakeModules):
  - in the corresponding `FindXXX.cmake` file (e.g., `FindSwifty-LLVM.cmake`) edit the `GIT_TAG` value to point to the SHA of the commit that should be included in Hylo;
  - create a PR with the changes, and ensure it's merged.
- In `hylo` repository:
  - in `TopLevelDefaults.cmake`, change the `GIT_TAG` value corresponding to `CMakeModules` repository to point to the SHA containing the change above;
  - run `swift package update XXX`, where `XXX` is the name of the package that needs to be updated (`Swift-LLVM` in our example); this will update `Package.resolved` file, with the SHA of the change that needs to be brought in;
  - double check that the SHA in `Package.resolved` matches the one that was written in the `CMakeModules` repository;
