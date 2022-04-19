// swift-tools-version:5.3
import PackageDescription

let package = Package(
  name: "Val",

  products: [
    .executable(name: "val", targets: ["CLI"]),
  ],

  dependencies: [
    .package(
      name: "swift-argument-parser",
      url: "https://github.com/apple/swift-argument-parser.git",
      from: "0.4.0")
  ],

  targets: [
    // The compiler's executable target.
    .target(
      name: "CLI",
      dependencies: [
        "Compiler",
        .product(name: "ArgumentParser", package: "swift-argument-parser"),
      ]),

    // Targets related to the compiler's internal library.
    .target(
      name: "Compiler",
      dependencies: ["Utils"]),
    .target(name: "Utils"),

    .target(name: "ParseGen", exclude: ["README.md"]),

    // Test targets.
    .testTarget(
      name: "ValTests",
      dependencies: ["Compiler"]),
  ])
