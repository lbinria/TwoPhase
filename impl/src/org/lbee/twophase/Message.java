package org.lbee.twophase;

public record Message(String sender, String content, long senderClock) { }
