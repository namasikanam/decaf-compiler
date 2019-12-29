import java.util.function.Function;

public class A {
    int field;

    public Function<Integer, Integer> getf(int local) {
        return new Function<Integer, Integer>() {
            @Override
            public Integer apply(Integer x) {
                return field + local + x;
            }
        };
    }

    public int callf() {
        return getf(10).apply(20);
    }
}