package org.lbee.twophase;

import java.util.Map;

public class TLARecordValue extends TLAValue {

    public void set(String key, String value) {
        Map.Entry<?, ?> entry = Map.entry(key, value);
        this.apply("ExceptAt", entry);
    }

}

