package org.lbee;

import java.util.Random;

public class Helper {

    public static Random random = new Random(42);

    public static int next(int bound) {
        return random.nextInt(bound);
    }

}
