package org.lbee.twophase;

import java.util.Map;

public class TLARecordVariable extends TLAVariable {

    public void set(String key, String value) {
        Map.Entry<?, ?> entry = Map.entry(key, value);
        this.apply("ExceptAt", entry);
    }

    @Override
    public String toString() {
        // TODO implement
        return super.toString();
    }
}

