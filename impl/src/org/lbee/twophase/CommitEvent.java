package org.lbee.twophase;

public interface CommitEvent {

    void setClock(long clock);
    void commit();

}
