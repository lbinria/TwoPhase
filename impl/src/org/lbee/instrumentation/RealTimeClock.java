package org.lbee.instrumentation;

public class RealTimeClock implements InstrumentationClock {

    @Override
    public void sync(long clock) {
        // Nothing to do
    }

    @Override
    public long getValue() {
        return System.currentTimeMillis();
    }
}
