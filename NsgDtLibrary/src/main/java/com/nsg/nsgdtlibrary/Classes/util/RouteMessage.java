package com.nsg.nsgdtlibrary.Classes.util;

import com.google.android.gms.maps.model.LatLng;

import java.util.List;
import java.util.Objects;

public class RouteMessage {
    private String message;
    private List<LatLng> line;

    public RouteMessage() {}

    public RouteMessage(String message, List<LatLng> line) {
        this.message = message;
        this.line = line;
    }

    public String getMessage() {
        return message;
    }

    public void setMessage(String message) {
        this.message = message;
    }

    public List<LatLng> getLine() {
        return line;
    }

    public void setLine(List<LatLng> line) {
        this.line = line;
    }

    @Override
    public boolean equals(Object o) {
        //TODO coordinate comparison
        if (this == o) return true;
        if (!(o instanceof RouteMessage)) return false;
        RouteMessage that = (RouteMessage) o;
        return getMessage().equals(that.getMessage()) &&
                getLine().equals(that.getLine());
    }

    @Override
    public int hashCode() {
        return getMessage().hashCode() + getLine().toString().hashCode();
    }
}
