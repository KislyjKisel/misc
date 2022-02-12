#include <iostream>
#include <algorithm>
#include <type_traits>
#include <vector>

namespace op {
    template<typename Lhs, typename Rhs, typename Out, typename F> requires std::is_invocable_r_v<Out, F, Lhs, Rhs>
    struct Binop { 
        constexpr friend auto operator<(const Lhs& lhs, const Binop& op) {
            return (struct {
                [[no_unique_address]] F f;
                const Lhs& lhs;

                constexpr Out operator>(const Rhs& rhs) {
                    return f(lhs, rhs);
                }
            }){ std::move(op.f), lhs };
        }

        constexpr Binop(F&& f) : f(std::forward<F>(f)) { }

    private:
        [[no_unique_address]] F f;
    };

    template<typename Lhs, typename Rhs, typename Out, typename F> requires std::is_invocable_r_v<Out, F, Lhs, Rhs>
    constexpr Binop<Lhs,Rhs,Out,F> make_binop(F&& f) { return Binop<Lhs, Rhs, Out, F>(std::forward<F>(f)); }
}

auto inside_of = op::make_binop<int, std::vector<int>, bool>([](int v, std::vector<int> xs) { return std::any_of(xs.begin(), xs.end(), [v](int x) { return x == v; } ); });
#define ϵ <inside_of>

int main() {
    std::vector<int> xs { 1, 2, 3, 4, 5 };
    std::cout << (6 ϵ xs ? "Yes" : "No") << '\n';
}