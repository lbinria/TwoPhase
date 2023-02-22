package org.lbee.twophase;

public class TLAStringValue extends TLAValue {

    public void set(String value) {
        this.apply("Replace", value);
    }

}
