load("//tools:defs.bzl", "go_library", "go_test")

package(licenses = ["notice"])

go_library(
    name = "wire",
    srcs = ["wire.go"],
    marshal = False,
    stateify = False,
    visibility = ["//:sandbox"],
    deps = ["//pkg/gohacks"],
)

go_test(
    name = "wire_test",
    size = "small",
    srcs = ["wire_test.go"],
    library = ":wire",
)
