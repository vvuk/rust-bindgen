

void top_level();

namespace whatever {
    typedef int whatever_int_t;

    void in_whatever();
}

namespace {
    namespace empty {}

    void foo();

    class A {
        whatever::whatever_int_t b;
    };
}

