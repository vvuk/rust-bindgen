

void top_level();

namespace whatever {
    typedef int whatever_int_t;

    void in_whatever();
}

namespace {
    namespace empty {}

    void foo();
    struct A {
        whatever::whatever_int_t b;
    public:
        int lets_hope_this_works();
    };
}

template<typename T>
class C: public A {
    T m_c;
};


template<>
class C<int>;


namespace w {

    template<typename T>
    class D {
        C<T> m_c;
        void wat();
    };

    C<int> foo();
}
