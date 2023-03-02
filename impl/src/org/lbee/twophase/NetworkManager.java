package org.lbee.twophase;

import org.lbee.instrumentation.FormalInstrumentation;
import org.lbee.instrumentation.FormalInstrumentationConfig;
import org.lbee.instrumentation.TraceProducerException;
import org.lbee.instrumentation.jfr.JFRTraceProducer;
import org.lbee.twophase.models.Message;

import java.io.*;
import java.net.Socket;

public abstract class NetworkManager implements NamedClient {

    private final InputStream inputStream;
    private final PrintWriter writer;

    protected final FormalInstrumentation<JFRTraceProducer> instrumentation;

    private boolean shutdown;

    public boolean isShutdown() { return shutdown; }
    protected void shutdown() { shutdown = true; }

    public NetworkManager(Socket socket) throws IOException {
        this.inputStream = socket.getInputStream();
        OutputStream outputStream = socket.getOutputStream();
        this.writer = new PrintWriter(outputStream, true);
        this.shutdown = false;
        instrumentation = new FormalInstrumentation<>(new FormalInstrumentationConfig("JFR", true), new JFRTraceProducer());
    }

    //abstract void run() throws IOException;

    protected void run() throws IOException, TraceProducerException {
        Message message = receive();

        if (message == null)
            return;

        System.out.printf("%s - %s receive message: `%s`...\n", this.instrumentation.getClock(), this.getName(), message.getContent());
        // Sync process clock
        this.instrumentation.getClock().sync(message.getSenderClock());

        // Call receive with received message
        receive(message);
    }

    abstract void receive(Message message) throws IOException, TraceProducerException;

    protected Message receive() throws IOException {
        // Request for message destined to me
        writer.println("r:" + this.getName());
        BufferedReader reader = new BufferedReader(new InputStreamReader(this.inputStream));
        String data = reader.readLine();
        if (data.equals("null"))
            return null;
        else {
            String[] components = data.split(";");
            return new Message(components);
        }
    }

    protected boolean send(Message message) throws IOException {
        // Log event (hard-coded for now)
        //logger.log(this, "msgs", message.getContent());
        //logger.commit();
        // Send message to server
        writer.println("s:" + message.toString());
        // Read response
        BufferedReader reader = new BufferedReader(new InputStreamReader(this.inputStream));
        String data = reader.readLine();
        return !data.equals("null");
    }

    protected void sendRaw(String s) {
        writer.println(s);
    }

}
