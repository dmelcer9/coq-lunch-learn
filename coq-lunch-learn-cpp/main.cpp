#include <iostream>

template<int Num, int SeqPos>
class Fibonacci;

template<>
class Fibonacci<1, 1> {
    const int value = 1;
};

template<>
class Fibonacci<1, 2> {
    const int value = 1;
};

template<int Num, int SeqPos>
class Fibonacci {
public:
    const int value = Num;

    template<int N>
    static Fibonacci add(Fibonacci<N, SeqPos - 2> f1, Fibonacci<Num - N, SeqPos - 1> f2) {
        return Fibonacci();
    }
};

int main() {
    auto f1 = Fibonacci<1, 1>();
    auto f2 = Fibonacci<1, 2>();
    auto f3 = Fibonacci<2, 3>::add(f1, f2);
    auto f4 = Fibonacci<3, 4>::add(f2, f3);
    auto f5 = Fibonacci<5, 5>::add(f3, f4);
    auto f6 = Fibonacci<8, 6>::add(f4, f5);
    std::cout << f6.value << std::endl;
}


Fibonacci<15, 20> weird(Fibonacci<7, 18> f18, Fibonacci<8, 19> f19) {
    Fibonacci<15, 20> f20 = Fibonacci<15, 20>::add(f18, f19);
}