package com.nsg.nsgdtlibrary.Classes.util;

import android.content.BroadcastReceiver;
import android.content.Context;
import android.content.Intent;
import android.location.Location;
import android.util.Log;

import com.google.android.gms.maps.model.LatLng;
/**
 * Receiver for broadcasts sent by {@link LocationUpdatesService}.
 */
public class LocationReceiver extends BroadcastReceiver {
    private NSGIMapFragmentActivity fragmentActivity;
    public LocationReceiver() {
        this.fragmentActivity = fragmentActivity;
    }

    public void setReference(NSGIMapFragmentActivity fragmentActivity) {
        this.fragmentActivity = fragmentActivity;
    }

    @Override
    public void onReceive(Context context, Intent intent) {
        Location location = intent.getParcelableExtra(LocationUpdatesService.EXTRA_LOCATION);
        if (location != null) {
           // Log.e("myreceiver", Utils.getLocationText(location));
            fragmentActivity.saveLocation(new LatLng(location.getLatitude(), location.getLongitude()));
        }
    }
}