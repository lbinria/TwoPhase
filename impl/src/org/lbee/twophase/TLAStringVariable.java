package org.lbee.twophase;

public class TLAStringVariable extends TLAVariable {

    public void set(String value) {
        this.apply("Replace", value);
    }

}
