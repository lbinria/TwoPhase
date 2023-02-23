package org.lbee.instrumentation;

public class FormalInstrumentationConfig {

    private final boolean logicClock;

    public FormalInstrumentationConfig(boolean logicClock) {
        this.logicClock = logicClock;
    }

    public boolean isLogicClock() {
        return logicClock;
    }
}
