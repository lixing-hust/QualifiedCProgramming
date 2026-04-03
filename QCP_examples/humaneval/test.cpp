#include <iostream>
#include <vector>
#include <cmath>

using namespace std;

void solve() {
    int n;
    cin >> n;
    vector<int> a(n);
    for (int i = 0; i < n; ++i) {
        cin >> a[i];
    }

    // 只有一个元素，长度就是 1
    if (n == 1) {
        cout << 1 << "\n";
        return;
    }

    // 1. 求出相邻元素的差值数组 d
    vector<int> d(n - 1);
    for (int i = 0; i < n - 1; ++i) {
        d[i] = abs(a[i + 1] - a[i]);
    }

    // ans[k] 记录最大差值不超过 k 时的子数组最大长度
    // 默认每个元素自己成一组，长度为 1
    vector<int> ans(n + 1, 1);
    vector<int> st; // 用 vector 模拟单调栈
    vector<int> left(n - 1, -1);
    vector<int> right(n - 1, n - 1);

    // 2. 单调栈：一次遍历找到每个 d[i] 左右两侧第一个比它大的位置
    for (int i = 0; i < n - 1; ++i) {
        while (!st.empty() && d[st.back()] <= d[i]) {
            right[st.back()] = i;
            st.pop_back();
        }
        if (!st.empty()) {
            left[i] = st.back();
        }
        st.push_back(i);
    }

    // 3. 将单调栈求出的区间长度，映射到对应的差值 k 上
    for (int i = 0; i < n - 1; ++i) {
        int k = d[i];
        if (k <= n) {
            // 连续差值个数为 right - left - 1，对应的子数组长度需 +1，即 right - left
            ans[k] = max(ans[k], right[i] - left[i]);
        }
    }

    // 4. 前缀最大值传递：如果 k=2 时能达到长度 3，那 k=3 时保底也是 3
    for (int k = 1; k <= n; ++k) {
        ans[k] = max(ans[k], ans[k - 1]);
        cout << ans[k] << (k == n ? "" : " ");
    }
    cout << "\n";
}

int main() {
    // 解绑流，保证输入输出速度极快
    ios_base::sync_with_stdio(false);
    cin.tie(NULL);
    
    int T;
    if (cin >> T) {
        while (T--) {
            solve();
        }
    }
    return 0;
}