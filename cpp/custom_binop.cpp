#include <type_traits>
#include <utility>

namespace op {
    // hidden
    template<typename Lhs, typename Rhs, typename Out, typename F>
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

        template<typename FF>
        constexpr Binop(FF&& f) : f(std::forward<FF>(f)) { }

    private:
        [[no_unique_address]] F f;
    };

    template<typename Lhs, typename Rhs, typename Out, typename F> requires std::is_invocable_r_v<Out, F, Lhs, Rhs>
    constexpr Binop<Lhs,Rhs,Out,F> make_binop(F&& f) { return Binop<Lhs, Rhs, Out, F>(std::forward<F>(f)); }
}


// Example

#include <algorithm>
#include <iostream>
#include <vector>

auto inside_of = op::make_binop<int, const std::vector<int>&, bool>(
    [](int v, const std::vector<int>& xs) {
        return std::any_of(xs.begin(), xs.end(), [v](int x) { return x == v; } );
    });

#define ϵ <inside_of>

int main() {
    std::vector<int> xs { 1, 2, 3, 4, 5 };

    std::cout << "xs = { ";
    for(auto x : xs) std::cout << x << ' ';
    std::cout << "}\n";

    const auto test = [&](int x){ std::cout << x << " ϵ xs ? " << (x ϵ xs ? "Yes" : "No") << "\n"; }; 
    test(3);
    test(7);
}