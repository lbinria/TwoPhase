package org.lbee.twophase;

public class TLARecordValue extends TLAValue {

    public void set(String value) {
        this.apply("ExceptAt", value);
    }

}

