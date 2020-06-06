load("//tools:defs.bzl", "go_library", "go_test")

package(licenses = ["notice"])

go_library(
    name = "ports",
    srcs = ["ports.go"],
    visibility = ["//visibility:public"],
    deps = [
        "//pkg/log",
        "//pkg/sync",
        "//pkg/tcpip",
    ],
)

go_test(
    name = "ports_test",
    srcs = ["ports_test.go"],
    library = ":ports",
    deps = [
        "//pkg/tcpip",
    ],
)
