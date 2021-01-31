package com.nsg.nsgdtlibrary.Classes.util;

import android.Manifest.permission;
import android.animation.ValueAnimator;
import android.annotation.SuppressLint;
import android.app.Activity;
import android.app.AlertDialog;
import android.content.ComponentName;
import android.content.Context;
import android.content.DialogInterface;
import android.content.Intent;
import android.content.IntentFilter;
import android.content.ServiceConnection;
import android.content.pm.PackageManager;
import android.graphics.Bitmap;
import android.graphics.BitmapFactory;
import android.graphics.Color;
import android.graphics.Matrix;
import android.graphics.Point;
import android.location.Location;
import android.location.LocationManager;
import android.os.Build;
import android.os.Bundle;
import android.os.Environment;
import android.os.Handler;
import android.os.IBinder;
import android.os.Looper;
import android.os.SystemClock;
import android.speech.tts.TextToSpeech;
import android.util.Log;
import android.view.Gravity;
import android.view.LayoutInflater;
import android.view.MenuItem;
import android.view.View;
import android.view.ViewGroup;
import android.view.animation.Interpolator;
import android.view.animation.LinearInterpolator;
import android.widget.ImageButton;
import android.widget.ImageView;
import android.widget.PopupMenu;
import android.widget.TextView;
import android.widget.Toast;

import androidx.annotation.NonNull;
import androidx.annotation.RequiresApi;
import androidx.core.app.ActivityCompat;
import androidx.core.content.ContextCompat;
import androidx.fragment.app.Fragment;
import androidx.localbroadcastmanager.content.LocalBroadcastManager;

import com.google.android.gms.maps.CameraUpdateFactory;
import com.google.android.gms.maps.GoogleMap;
import com.google.android.gms.maps.OnMapReadyCallback;
import com.google.android.gms.maps.Projection;
import com.google.android.gms.maps.SupportMapFragment;
import com.google.android.gms.maps.model.CameraPosition;
import com.google.android.gms.maps.model.Circle;
import com.google.android.gms.maps.model.CircleOptions;
import com.google.android.gms.maps.model.LatLng;
import com.google.android.gms.maps.model.MapStyleOptions;
import com.google.android.gms.maps.model.Marker;
import com.google.android.gms.maps.model.MarkerOptions;
import com.google.android.gms.maps.model.Polyline;
import com.google.android.gms.maps.model.PolylineOptions;
import com.google.android.gms.maps.model.TileOverlay;
import com.google.android.gms.maps.model.TileOverlayOptions;
import com.google.android.gms.maps.model.TileProvider;
import com.google.maps.android.PolyUtil;
import com.google.maps.android.SphericalUtil;
import com.nsg.nsgdtlibrary.Classes.activities.AppConstants;
import com.nsg.nsgdtlibrary.Classes.activities.ExpandedMBTilesTileProvider;
import com.nsg.nsgdtlibrary.Classes.activities.GpsUtils;
import com.nsg.nsgdtlibrary.Classes.database.dto.EdgeDataT;
import com.nsg.nsgdtlibrary.Classes.database.dto.RouteT;
import com.nsg.nsgdtlibrary.R;

import org.json.JSONArray;
import org.json.JSONException;
import org.json.JSONObject;

import java.io.File;
import java.io.IOException;
import java.util.ArrayList;
import java.util.List;
import java.util.Locale;
import java.util.Objects;
import java.util.Timer;
import java.util.TimerTask;

import static android.Manifest.permission.ACCESS_FINE_LOCATION;
import static android.Manifest.permission.READ_EXTERNAL_STORAGE;
import static com.nsg.nsgdtlibrary.Classes.util.Utils.bearingBetweenLocations;
import static com.nsg.nsgdtlibrary.Classes.util.Utils.bitmapDescriptorFromVector;
import static com.nsg.nsgdtlibrary.Classes.util.Utils.calculateDistanceAlongLineFromStart;
import static com.nsg.nsgdtlibrary.Classes.util.Utils.cloneCoordinate;
import static com.nsg.nsgdtlibrary.Classes.util.Utils.cloneCoordinates;
import static com.nsg.nsgdtlibrary.Classes.util.Utils.computeRotation;
import static com.nsg.nsgdtlibrary.Classes.util.Utils.distFrom;
import static com.nsg.nsgdtlibrary.Classes.util.Utils.findNearestPointOnLine;
import static com.nsg.nsgdtlibrary.Classes.util.Utils.getAngle;
import static com.nsg.nsgdtlibrary.Classes.util.Utils.mergeRoutes;
import static com.nsg.nsgdtlibrary.Classes.util.Utils.pointWithinPolygon;
import static com.nsg.nsgdtlibrary.Classes.util.Utils.removeDuplicatesRouteDeviated;
import static com.nsg.nsgdtlibrary.Classes.util.Utils.reverseCoordinate;
import static com.nsg.nsgdtlibrary.Classes.util.Utils.reverseCoordinates;
import static com.nsg.nsgdtlibrary.Classes.util.Utils.setEstimatedTime;
import static com.nsg.nsgdtlibrary.Classes.util.Utils.showDistance;
import static com.nsg.nsgdtlibrary.Classes.util.Utils.splitLineByPoint;

public class NSGIMapFragmentActivity extends Fragment implements View.OnClickListener {
    private boolean isWriteLogFile = false;
    private boolean isAlertShown = false;
    private static final int PERMISSION_REQUEST_CODE = 200;
    boolean locationAccepted, islocationControlEnabled = false;
    // private static final int SENSOR_DELAY_NORMAL =50;
    private TextToSpeech textToSpeech = null;

    // do not use this directly
    LatLng lastGPSPosition = null;

    LatLng oldGPSPosition;
    Marker mPositionMarker;
    private GoogleMap mMap;
    private List points;
    private List<LatLng> convertedPoints;
    private Marker sourceMarker, destinationMarker;

    private int routeDeviationDistance;
    private Circle mCircle = null;
    Bitmap mMarkerIcon;

    private final List<LatLng> currentRouteData = new ArrayList<LatLng>();
    private final List<LatLng> currentDeviatedRouteData = new ArrayList<>();
    private final List<LatLng> deviatedRouteData = new ArrayList<>();

    private List<LatLng> nearestPointValuesList;
    private ImageButton change_map_options, re_center;
    private List<LatLng> OldNearestGpsList;
    private String BASE_MAP_URL_FORMAT;
    private LatLng SourceNode, DestinationNode;
    LatLng currentGpsPosition;
    float azimuthInDegress;
    Timer myTimer = null;
    private String stNode, endNode, routeDeviatedDT_URL = "", AuthorisationKey;
    double TotalDistanceInMTS;
    LatLng currentPerpendicularPoint = null;
    private String routeData;
    public boolean isMapLoaded = false;
    public boolean isNavigationStarted = false;

    private double wayLatitude = 0.0, wayLongitude = 0.0;
    private boolean isContinue = true;
    private String GeoFenceCordinates;
    private boolean routeAPIHit = false;
    final List<LatLng> commonPoints = new ArrayList<LatLng>();
    final List<LatLng> uncommonPoints = new ArrayList<LatLng>();

    //
    final List<Double> consDistList = new ArrayList<>();
    List<LatLng> destinationGeoFenceCoordinatesList;
    private boolean isLieInGeofence = false;
    private boolean isContinuoslyOutOfTrack = false;
//    private EditText dynamic_changeValue;
//    private Button submit;

    long startTimestamp;
    int estimatedRemainingTime = 0;

    private static int CURRENT_ROUTE_COLOR = Color.CYAN;
    private static int DEVIATED_ROUTE_COLOR = Color.RED;

    private static int CURRENT_ROUTE_WIDTH = 25;
    private static int DEVIATED_ROUTE_WIDTH = 25;

    List<RouteMessage> messageContainer = new ArrayList<>();

    List<RouteMessage> messageContainerTemp = new ArrayList<>();

    PolylineOptions currentPolylineOptions = new PolylineOptions();
    Polyline currentPolylineGraphics = null;

    PolylineOptions deviatedPolylineOptions = new PolylineOptions();
    Polyline deviatedPolylineGraphics = null;

    private static double MINIMUM_VEHICLE_SPEED = 30d; // KM/HR

    private int estimatedTimeInSeconds = 0;
    public static int AVERAGE_SPEED = 30;

    private boolean isETACrossed = false;

    private List<EdgeDataT> edgeDataList;

    private LatLng nearlyFirstGPSPosition = null;

    private boolean isFragmentDestroyed = false;

    //-- new change start

    // The BroadcastReceiver used to listen from broadcasts from the service.
    private LocationReceiver myReceiver;

    // A reference to the service used to get location updates.
    private LocationUpdatesService locationUpdatesService = null;

    // Tracks the bound state of the service.
    private boolean mBound = false;

    // Monitors the state of the connection to the service.
    private final ServiceConnection mServiceConnection = new ServiceConnection() {

        @Override
        public void onServiceConnected(ComponentName name, IBinder service) {

            Log.i("service bind", "success");

            LocalBinder binder = (LocalBinder) service;
            locationUpdatesService = binder.getService();
            mBound = true;
            locationUpdatesService.requestLocationUpdates();
        }

        @Override
        public void onServiceDisconnected(ComponentName name) {
            Log.i("service unbind", "success");
            locationUpdatesService.removeLocationUpdates();
            locationUpdatesService = null;
            mBound = false;
        }
    };
    private SupportMapFragment mapFragment;
    private AsyncResponse asyncResponse;
    private Runnable startNavigationRunnable = null;
    private Handler startNavigationHandler = null;
    private Handler animateCarMoveHandler = null;
    private Runnable animateCarMoveRunnable = null;
    private Handler animateCarMoveNotUpdateMarkerHandler = null;
    private Runnable animateCarMoveNotUpdateMarkerRunnable = null;
    private PopupMenu popup;

    //-- new change end

    public interface FragmentToActivity {
        String communicate(String comm, int alertType);
    }

//    private FragmentToActivity Callback;

    public NSGIMapFragmentActivity() {
    }

    @SuppressLint("ValidFragment")
    public NSGIMapFragmentActivity(String BASE_MAP_URL_FORMAT) {
        this.BASE_MAP_URL_FORMAT = BASE_MAP_URL_FORMAT;
    }

    public static NSGIMapFragmentActivity getInstance(String BASE_MAP_URL_FORMAT) {
        return new NSGIMapFragmentActivity(BASE_MAP_URL_FORMAT);
    }

    public static NSGIMapFragmentActivity getInstance(String BASE_MAP_URL_FORMAT, String stNode, String endNode, String routeData, int routeDeviationBuffer, String routeDeviatedDT_URL, String AuthorisationKey, String geoFenceCoordinates, boolean isWriteLogFile) {
        return new NSGIMapFragmentActivity(BASE_MAP_URL_FORMAT, stNode, endNode, routeData, routeDeviationBuffer, routeDeviatedDT_URL, AuthorisationKey, geoFenceCoordinates, isWriteLogFile);
    }

    @SuppressLint("ValidFragment")
    public NSGIMapFragmentActivity(String BASE_MAP_URL_FORMAT, String stNode, String endNode, String routeData, int routeDeviationBuffer, String routeDeviatedDT_URL, String AuthorisationKey, String GeoFenceCordinates, boolean isWriteLogFile) {
        this.BASE_MAP_URL_FORMAT = BASE_MAP_URL_FORMAT;
        this.stNode = stNode;
        this.endNode = endNode;
        this.routeDeviationDistance = routeDeviationBuffer;
        this.routeData = routeData;
        this.routeDeviatedDT_URL = routeDeviatedDT_URL;
        this.AuthorisationKey = AuthorisationKey;
        this.GeoFenceCordinates = GeoFenceCordinates;
        this.isWriteLogFile = isWriteLogFile;
    }

    private LatLng getLastGPSPosition() {

        if (lastGPSPosition == null) {
            return null;
        } else {
            return new LatLng(lastGPSPosition.latitude, lastGPSPosition.longitude);
        }
    }


    @Override
    public void onStart() {

        getContext().bindService(new Intent(getContext(), LocationUpdatesService.class), mServiceConnection,
                Context.BIND_AUTO_CREATE);

        super.onStart();
    }

    @Override
    public void onStop() {
        super.onStop();
        if (mBound) {
            // Unbind from the service. This signals to the service that this activity is no longer
            // in the foreground, and the service can respond by promoting itself to a foreground
            // service.
            getContext().unbindService(mServiceConnection);
            mBound = false;
        }
    }

    @Override
    public void onResume() {
        super.onResume();
        LocalBroadcastManager.getInstance(getContext()).registerReceiver(myReceiver,
                new IntentFilter(LocationUpdatesService.ACTION_BROADCAST));
//        locationUpdatesService.requestLocationUpdates();
    }

    @Override
    public void onPause() {
        LocalBroadcastManager.getInstance(getContext()).unregisterReceiver(myReceiver);
//        locationUpdatesService.removeLocationUpdates();
        super.onPause();
    }

    void startTTS() {
        final Activity tmpActivity = getActivity();
        if(tmpActivity != null) {
            final Context context = tmpActivity.getApplicationContext();
            if(context != null) {
                textToSpeech = new TextToSpeech(context, new TextToSpeech.OnInitListener() {
                    @Override
                    public void onInit(int status) {
                        if (status == TextToSpeech.SUCCESS) {
                            int ttsLang = textToSpeech.setLanguage(Locale.US);
                            if (ttsLang == TextToSpeech.LANG_MISSING_DATA
                                    || ttsLang == TextToSpeech.LANG_NOT_SUPPORTED) {
                                Log.e("TTS", "The Language is not supported!");
                            } else {
                                Log.i("TTS", "Language Supported.");
                            }
                            Log.i("TTS", "Initialization success.");
                        } else {
                            Toast.makeText(getContext(), "TTS Initialization failed!", Toast.LENGTH_SHORT).show();
                        }
                    }
                });
            }
        }

    }

    void stopTTS() {
        if (textToSpeech != null) {
            textToSpeech.stop();
            textToSpeech.shutdown();
            textToSpeech = null;
        }
    }

    @Override
    public void onCreate(Bundle savedInstanceState) {
        super.onCreate(savedInstanceState);
        setHasOptionsMenu(true);

        myReceiver = new LocationReceiver(this);

        //mLocationManager = (LocationManager) getActivity().getSystemService(LOCATION_SERVICE);


        new GpsUtils(getContext()).turnGPSOn(new GpsUtils.onGpsListener() {
            @Override
            public void gpsStatus(boolean isGPSEnable) {
                // turn on GPS
//                isGPS = isGPSEnable;
            }
        });

    }

    @Override
    public void onAttach(Context context) {
        super.onAttach(context);
        startTTS();
//        try {
//            //sqlHandler = new SqlHandler(getContext());// Sqlite handler
//            Callback = (FragmentToActivity) context;
//        } catch (ClassCastException e) {
//            Log.e("ON ATTACH", e.getMessage(), e);
//            throw new ClassCastException(context.toString()
//                    + " must implement FragmentToActivity");
//        }
    }

    @Override
    public void onDestroyView() {
        super.onDestroyView();
        Log.i("onDestroyView", "called");
        unInitializeAllHandler();
        if(mMap != null) {
            mMap.clear();
        }

        if(re_center != null) {
            re_center.setOnClickListener(null);
        }

        if(popup != null) {
            popup.setOnMenuItemClickListener(null);
            popup = null;
        }

        if(change_map_options != null) {
            change_map_options.setOnClickListener(null);
        }
        if(mapFragment != null) {
            mapFragment.onDestroyView();
        }
        if(sourceMarker != null) {
            sourceMarker.remove();
        }
        if(destinationMarker != null) {
            destinationMarker.remove();
        }

    }

    void deInitializeView() {
        mMap = null;
        mPositionMarker = null;
        mMarkerIcon = null;
        re_center = null;

        if(popup != null) {
            popup.setOnMenuItemClickListener(null);
            popup = null;
        }

        change_map_options = null;
        mapFragment.onDestroy();
        mapFragment = null;
        sourceMarker = null;
        destinationMarker = null;
        mCircle = null;
    }

    @RequiresApi(api = Build.VERSION_CODES.KITKAT)
    @Override
    public View onCreateView(LayoutInflater inflater, ViewGroup container,
                             Bundle savedInstanceState) {
        //Check self permissions for Location and storage
        if (!checkPermission()) {
            //Request permissions for Location and storage
            requestPermission();
        }
        //set marker icon
        mMarkerIcon = BitmapFactory.decodeResource(getResources(), R.drawable.gps_transperent_98);
        //Initialise RootView
        View rootView = inflater.inflate(R.layout.fragment_map, container, false);
        //If writeLogFile==true then writing logs on file otherwise we can't write log files on filestorage ---
        if (isWriteLogFile) {
            writeLogFile();
        }

        //Initialise Buttons

        // dynamic_changeValue = (EditText) rootView.findViewById(R.id.dynamic_buffer);
        //  submit = (Button) rootView.findViewById(R.id.submit);
        //  submit.setOnClickListener(NSGIMapFragmentActivity.this);
        re_center = (ImageButton) rootView.findViewById(R.id.re_center);
        re_center.setOnClickListener(NSGIMapFragmentActivity.this);
        change_map_options = (ImageButton) rootView.findViewById(R.id.change_map_options);
        change_map_options.setOnClickListener(NSGIMapFragmentActivity.this);
        // Delete Contents fron ROUTE_T On initialisation of Route view
        String delQuery = "DELETE  FROM " + RouteT.TABLE_NAME;
//        sqlHandler.executeQuery(delQuery);
        /* Insert NewDatata According to  SourceNode,DestinationNode,RouteData To local Database Coloumns*/
//        if (stNode != null && endNode != null && routeData != null) {
//            InsertAllRouteData(stNode, endNode, routeData);
//            getRouteAccordingToRouteID(stNode, endNode);
//            if (RouteDataList != null && RouteDataList.size() > 0) {
//                route = RouteDataList.get(0);
//                String routeDataFrmLocalDB = route.getRouteData();
//                String sourceText = route.getStartNode();
//                String[] text = sourceText.split(" ");
//                sourceLat = Double.parseDouble(text[1]);
//                sourceLng = Double.parseDouble(text[0]);
//                String destinationText = route.getEndNode();
//                String[] text1 = destinationText.split(" ");
//                destLat = Double.parseDouble(text1[1]);
//                destLng = Double.parseDouble(text1[0]);
//            }
//        }
        //Initialise Map fragment
        mapFragment = (SupportMapFragment) getChildFragmentManager().findFragmentById(R.id.frg);  //use SuppoprtMapFragment for using in fragment instead of activity  MapFragment1 = activity   SupportMapFragment = fragment
        mapFragment.getMapAsync(new OnMapReadyCallback() {
            @Override
            public void onMapReady(GoogleMap googlemap) {
                if (BASE_MAP_URL_FORMAT != null) {
                    //Initialise GoogleMap
                    NSGIMapFragmentActivity.this.mMap = googlemap;
                    //mMap.setMapType(GoogleMap.MAP_TYPE_NONE);
                    //set GoogleMap Style
                    NSGIMapFragmentActivity.this.mMap.setMapStyle(MapStyleOptions.loadRawResourceStyle(getContext(), R.raw.stle_map_json));
                    //set  Tileprovider to GoogleMap
                    TileProvider tileProvider = new ExpandedMBTilesTileProvider(new File(BASE_MAP_URL_FORMAT.toString()), 256, 256);
                    TileOverlay tileOverlay = mMap.addTileOverlay(new TileOverlayOptions().tileProvider(tileProvider));
                    tileOverlay.setTransparency(0.5f - tileOverlay.getTransparency());
                    tileOverlay.setVisible(true);
                    if (routeData != null) {
                        /*Get Route From Database and plot on map*/
                        GetRouteFromDBPlotOnMap(routeData);
                        StringBuilder routeAlert = new StringBuilder();
                        routeAlert.append(MapEvents.ALERTVALUE_1).append("SourcePosition : " + SourceNode).append("Destination Node " + DestinationNode);
                        //send alert AlertTupe-1 -- started
                        sendData(routeAlert.toString(), MapEvents.ALERTTYPE_1);
                    }
                    //get all edges data from local DB
//                    getAllEdgesData();
                    // get Valid Routedata acc to Map
//                    try {
//                        getValidRouteData();
//                    } catch (JSONException e) {
//                        e.printStackTrace();
//                        Log.e("getValidRouteData: ", e.getMessage(), e);
//                    }
                    //Adding markers on map
                    addMarkers();
                    if (GeoFenceCordinates != null && !GeoFenceCordinates.isEmpty()) {
                        SplitDestinationData(GeoFenceCordinates);
                    }
                    if (ActivityCompat.checkSelfPermission(getContext(), ACCESS_FINE_LOCATION) != PackageManager.PERMISSION_GRANTED && ActivityCompat.checkSelfPermission(getContext(), permission.ACCESS_COARSE_LOCATION) != PackageManager.PERMISSION_GRANTED) {
                        // TODO: Consider calling
                        //    ActivityCompat#requestPermissions
                        return;
                    }
                    //Sending Alert Map is READY
                    isMapLoaded = true;
                    if (isMapLoaded) {
                        String MapAlert = "Map is Ready";
                        sendData(MapEvents.ALERTVALUE_6, MapEvents.ALERTTYPE_6);
                    }


                }
            }
        });
        return rootView;
    }

    @SuppressLint("MissingPermission")
    @Override
    public void onClick(View v) {
        if (v.getId() == R.id.change_map_options) {
                /*
                Changing Map options on button click To MAP_TYPE_NORMAL,MAP_TYPE_SATELLITE,MAP_TYPE_TERRAIN,MAP_TYPE_HYBRID
                 */
            if(popup == null) {
                popup = new PopupMenu(getContext(), change_map_options);
                //Inflating the Popup using xml file
                popup.getMenuInflater()
                        .inflate(R.menu.popup_menu, popup.getMenu());
                //registering popup with OnMenuItemClickListener
                popup.setOnMenuItemClickListener(new PopupMenu.OnMenuItemClickListener() {
                    public boolean onMenuItemClick(MenuItem item) {
                        int itemId = item.getItemId();
                        if (itemId == R.id.slot1) {
                            if (mMap != null) {
                                mMap.setMapType(GoogleMap.MAP_TYPE_NORMAL);
                                //  Toast.makeText(getContext(), "NORMAL MAP ENABLED", Toast.LENGTH_SHORT).show();
                            }
                            return true;
                        } else if (itemId == R.id.slot2) {
                            if (mMap != null) {
                                mMap.setMapType(GoogleMap.MAP_TYPE_SATELLITE);
                                //  Toast.makeText(getContext(), "SATELLITE MAP ENABLED", Toast.LENGTH_SHORT).show();
                            }
                            return true;
                        } else if (itemId == R.id.slot3) {
                            if (mMap != null) {
                                mMap.setMapType(GoogleMap.MAP_TYPE_TERRAIN);
                                // Toast.makeText(getContext(), "TERRAIN MAP ENABLED", Toast.LENGTH_SHORT).show();
                            }
                            return true;
                        } else if (itemId == R.id.slot4) {
                            if (mMap != null) {
                                mMap.setMapType(GoogleMap.MAP_TYPE_HYBRID);
                                //  Toast.makeText(getContext(), "HYBRID MAP ENABLED", Toast.LENGTH_SHORT).show();
                            }
                            return true;
                        }
                        return true;
                    }
                });
            }

            popup.show();
        } else if (v.getId() == R.id.re_center) {
                /*
                Recenter Button if map enabled and location enabled get location from map and update map position and
                recenter to  the position captured
                 */
            mMap.setMyLocationEnabled(true);
            if (mPositionMarker != null) {
                LatLng myLocation = null;
                myLocation = mPositionMarker.getPosition();
                int height = 0;
                if (getView() != null) {
                    height = getView().getMeasuredHeight();
                }
                mMap.moveCamera(CameraUpdateFactory.newLatLng(myLocation));
                mMap.animateCamera(CameraUpdateFactory.zoomTo(18));
            }
        }

//        else if (v.equals(submit)) {
//            if (!dynamic_changeValue.getText().toString().isEmpty()) {
//                int val = Integer.parseInt(dynamic_changeValue.getText().toString());
//                routeDeviationDistance = val;
//                Log.e("Route Deviation Buffer", " Deviation Buffer Test---- " + routeDeviationDistance);
//            } else {
//                routeDeviationDistance = 10;
//            }
//        }
    }

    //Main method to start the navigation
    @SuppressLint("MissingPermission")
    public int startNavigation() {
            /*
                Starts Navigation HERE
                Get current location from the location service if map enabled true then it will starts navigation
                from external service and strts navigation if route deviation not observed move in the loaded path
                if route deviation observed movement from route deviated path only
             */

        islocationControlEnabled = false;
        Log.v("APP DATA ", "islocationControlEnabled START BUTTON GPS POSITION ----" + oldGPSPosition);


        if (SourceNode != null && DestinationNode != null) {

            //estimate the projected travelling time
            estimatedTimeInSeconds = setEstimatedTime(currentRouteData);

            isETACrossed = false;

            //Construct Point based on main app passed Lat/Long
            nearestPointValuesList = new ArrayList<LatLng>();
            nearestPointValuesList.add(new LatLng(SourceNode.latitude, SourceNode.longitude));

            //Construct Point based on main app passed Lat/Long
            OldNearestGpsList = new ArrayList<>();
            OldNearestGpsList.add(new LatLng(SourceNode.latitude, SourceNode.longitude));


            try {

                if (mMap != null && isMapLoaded && !isNavigationStarted) {

                    //To enable Direction text for every 8000ms
                    isLieInGeofence = false;
                    if (myTimer == null) {
                        myTimer = new Timer();
                    }

                    myTimer.scheduleAtFixedRate(new TimerTask() {
                        @Override
                        public void run() {
                            if (currentGpsPosition != null && DestinationNode != null && isNavigationStarted) {
                                if (!islocationControlEnabled && !isContinuoslyOutOfTrack) {

                                    displayNavigationMessage(currentGpsPosition);
                                    // if (time != null && !time.toString().isEmpty() && estimatedRemainingTime > 0) {
                                    // ETA Calculation

                                    if (estimatedRemainingTime > 0) {
                                        if (getActivity() != null) {
                                            new Handler(Looper.getMainLooper()).post(new Runnable() {
                                                @Override
                                                public void run() {
                                                    String etaMessage = "";
                                                    if (estimatedRemainingTime > 60) {
                                                        int minute = estimatedRemainingTime / 60;
                                                        int sec = estimatedRemainingTime % 60;
                                                        etaMessage = "ETA: " + minute + "min. " + sec + "sec";
                                                    } else {
                                                        etaMessage = "ETA: " + estimatedRemainingTime + "sec";
                                                    }
                                                    final Activity tmpActivity = getActivity();
                                                    if(tmpActivity != null) {
                                                        final Context context = tmpActivity.getApplicationContext();
                                                        if(context != null) {
                                                            Toast toast = Toast.makeText(context, etaMessage, Toast.LENGTH_SHORT);
                                                            toast.setMargin(70, 50);
                                                            toast.setGravity(Gravity.BOTTOM, 0, 120);
                                                            if (isETACrossed) {
                                                                toast.getView().setBackgroundColor(Color.RED);
                                                            }
                                                            toast.show();
                                                        }
                                                    }

                                                }
                                            });
                                        }
                                    }

                                }

                            }
                        }

                    }, 10L, 8000L);
//                    } //end of Timer if

                    mMap.setMyLocationEnabled(true);
                    mMap.setBuildingsEnabled(true);
                    mMap.getUiSettings().setZoomControlsEnabled(true);
                    mMap.getUiSettings().setCompassEnabled(true);
                    //  mMap.getUiSettings().setMyLocationButtonEnabled(false);
                    mMap.getUiSettings().setMapToolbarEnabled(true);
                    mMap.getUiSettings().setZoomGesturesEnabled(true);
                    mMap.getUiSettings().setScrollGesturesEnabled(true);
                    mMap.getUiSettings().setTiltGesturesEnabled(true);
                    mMap.getUiSettings().setRotateGesturesEnabled(true);
                    mMap.getUiSettings().setMyLocationButtonEnabled(true);

                    //BY DEFAULT true
                    isNavigationStarted = true;

                    if (Build.VERSION.SDK_INT >= Build.VERSION_CODES.JELLY_BEAN) {
//                        if(startNavigationHandler == null) {
//                            startNavigationHandler = new Handler();
//                        }
                        final Handler tmpHandler = new Handler(Looper.getMainLooper());

                        //Get Location for every 1000 ms
                        int delay = 1000 * 1; //milliseconds

//                        if (startNavigationRunnable == null) {
//                            startNavigationRunnable = ;
//                        }

                        if (isNavigationStarted && !isFragmentDestroyed) {
                            tmpHandler.postDelayed(new Runnable() {
                                public void run() {
                                    double returnedDistance_ref = 0.0;

                                    if(mMap == null) {
                                        return;
                                    }

                                    if (currentGpsPosition != null) {
                                        oldGPSPosition = currentGpsPosition;
                                        //  Log.v("APP DATA ", "START NAV OLD GPS POSITION ----" + OldGPSPosition);
                                        // returnedDistance_ref = verifyDeviationCalculateDistance(OldGPSPosition, currentGpsPosition);
                                        LatLng nearest_LatLng_deviation = findNearestPointOnLine(currentRouteData, currentGpsPosition);
                                        if (nearest_LatLng_deviation != null) {
                                            returnedDistance_ref = SphericalUtil.computeDistanceBetween(currentGpsPosition, nearest_LatLng_deviation);
                                        }
                                    }

                                    consDistList.add(returnedDistance_ref);
                                    isContinue = true;

                                    currentGpsPosition = getLastGPSPosition();

                                    //Draw circle at current GPS with buffer configured value
                                    //ACTION - CHANGES TO BE DONE

                                    if (currentGpsPosition != null) {
                                        Log.v("APP DATA ", "START NAVI CURRENT GPS POSITION ----" + currentGpsPosition);
                                        //Draw Circle first time and update position next time
                                        // drawMarkerWithCircle(currentGpsPosition, routeDeviationDistance);
                                    }

                                    // Navigation code starts from here

                                    //OldNearestPosition means previous point on road
                                    LatLng OldNearestPosition = null;

                                    if (oldGPSPosition != null) {

                                        //Start of the tracking
                                        if (startTimestamp == 0) {
                                            // for the first time only
                                            startTimestamp = System.currentTimeMillis();
                                        }

                                        int timeTakenTillNow = (int) (System.currentTimeMillis() - startTimestamp) / 1000;

                                        // Taking sample of current GPS position, to know from where we have started the journey
                                        if (timeTakenTillNow < 5) {
                                            nearlyFirstGPSPosition = cloneCoordinate(currentGpsPosition);
                                        }

                                        //Get the distance between
                                        double distance = distFrom(oldGPSPosition.latitude, oldGPSPosition.longitude, currentGpsPosition.latitude, currentGpsPosition.longitude);
                                        //  Log.e("distance", "distance" + distance);

                                        //if the distance between previous GPS position and current GPS position is more than 40 meters
                                        //DONT DO ANYTHING - JUST SKIP THE POINT
                                        //WHY 40 METERS? - ACTION - CHECK
                                        if (distance > 40) {

                                        } else {

                                            //currentPerpendicularPoint ---- BY DEFAULT NULL
                                            OldNearestPosition = currentPerpendicularPoint;
                                            // Log.e("CurrentGpsPoint", " OLD Nearest GpsPoint " + OldNearestPosition);

                                            currentPerpendicularPoint = findNearestPointOnLine(currentRouteData, currentGpsPosition);

                                            Log.e("CurrentGpsPoint", " Nearest GpsPoint" + currentPerpendicularPoint);

                                            //Get the perpendicular distance from GPS to Road
                                            double distance_movement = distFrom(currentPerpendicularPoint.latitude, currentPerpendicularPoint.longitude, currentGpsPosition.latitude, currentGpsPosition.longitude);

                                            //If the perpendicular distance between current GPS and road is less than 40 meters
                                            //change the position of marker to point on road
                                            //ACTION - CHANGE THIS TO BUFFER DISTANCE


                                            if (distance_movement < 40) { //Follow current route

                                                Log.e("ORGINAL DATA ", " ORIGINAL DATA----" + currentGpsPosition + "," + currentPerpendicularPoint + "," + distance_movement);

                                                if(mMap == null) {
                                                    return;
                                                }
                                                //If there is no marker - create marker
                                                if (mPositionMarker == null && currentGpsPosition != null) {
                                                    mPositionMarker = mMap.addMarker(new MarkerOptions()
                                                            .position(SourceNode)
                                                            .title("Nearest GpsPoint")
                                                            .anchor(0.5f, 0.5f)
                                                            .flat(true)
                                                            .icon(bitmapDescriptorFromVector(getContext(), R.drawable.gps_transperent_98)));
                                                } else { //update marker position
                                                    // Log.e("CurrentGpsPoint", " currentGpsPosition ------ " + currentGpsPosition);

                                                    if(mPositionMarker == null || mMap == null) {
                                                        return;
                                                    }
                                                    if (OldNearestPosition != null) {
                                                        if (!islocationControlEnabled) {
                                                            Log.e("CurrentGpsPoint", " curren FRM START NAVI ------ " + currentGpsPosition);
                                                            // Log.e("CurrentGpsPoint", " Old  FRM START NAVI ------ " + OldNearestPosition);
                                                            Log.e("CurrentGpsPoint", " CGPS " + currentGpsPosition);
                                                            Log.e("CurrentGpsPoint", " per.CGPS " + currentPerpendicularPoint);


                                                            //moving the marker position from old point on road to new point on road in 1000ms
                                                            animateCarMove(mPositionMarker, OldNearestPosition, currentPerpendicularPoint, 1000);
                                                            float bearing = (float) bearingBetweenLocations(OldNearestPosition, currentPerpendicularPoint);
                                                            Log.e("MainRoute", "BEARING @@@@@@@ " + bearing);
                                                            int height = 0;
                                                            if (getView() != null) {
                                                                height = getView().getMeasuredHeight();
                                                            }
                                                            Projection p = mMap.getProjection();
                                                            Point bottomRightPoint = p.toScreenLocation(p.getVisibleRegion().nearRight);
                                                            Point center = new Point(bottomRightPoint.x / 2, bottomRightPoint.y / 2);
                                                            Point offset = new Point(center.x, (center.y + (height / 4)));
                                                            LatLng centerLoc = p.fromScreenLocation(center);
                                                            Log.e("MainRoute", "centerLoc @@@@@@@ " + centerLoc);

                                                            LatLng offsetNewLoc = p.fromScreenLocation(offset);
                                                            double offsetDistance = SphericalUtil.computeDistanceBetween(centerLoc, offsetNewLoc);
                                                            Log.e("MainRoute", "offsetDistance @@@@@@@ " + offsetDistance);
                                                            LatLng shadowTgt = SphericalUtil.computeOffset(currentPerpendicularPoint, offsetDistance, bearing);
                                                            Log.e("MainRoute", "shadowTgt @@@@@@@ " + shadowTgt);

                                                            //ETA Calculation
                                                            //  calculateETA(startTimestamp, currentGpsPosition, currentRouteData);
                                                            if (timeTakenTillNow >= 5) {
                                                                calculateETA(startTimestamp, currentGpsPosition, currentRouteData);
                                                            }
                                                            //*****************************************
                                                            //If vehicle reaches destination
                                                            alertDestination(currentGpsPosition);
                                                            //isReachedDestination(currentPerpendicularPoint, DestinationNode);
                                                            //*****************************************

                                                            if (offsetDistance > 5d && bearing > 0f  && mMap != null) {
                                                                CameraPosition currentPlace = new CameraPosition.Builder()
                                                                        .target(shadowTgt)
                                                                        .bearing(bearing).tilt(65.5f).zoom(18)
                                                                        .build();
                                                                mMap.animateCamera(CameraUpdateFactory.newCameraPosition(currentPlace), 1000, null);
                                                            }
                                                        } else {
//                                                            animateCarMoveNotUpdateMarker(mPositionMarker, OldNearestPosition, currentPerpendicularPoint, 1000);
                                                        }


                                                    } else {
                                                        // may be we need add marker animation here
                                                        //TODO
                                                    }
                                                }

                                            } else { //if the perpendicular distance is more than 40 (i.e. vehicle deviated the route) (** i.e. vehicle may be deviated the route)


                                                Log.e("DEVIATION DATA ", " DEVIATION DATA----" + currentGpsPosition + "," + currentPerpendicularPoint + "," + distance_movement);

                                                // will solve the move back issue, may be
                                                currentPerpendicularPoint = null;

                                                isContinuoslyOutOfTrack = false;
                                                if(mMap == null) {
                                                    return;
                                                }
                                                //Add marker first time
                                                if (mPositionMarker == null) {

                                                    mPositionMarker = mMap.addMarker(new MarkerOptions()
                                                            .position(currentGpsPosition)
                                                            .title("Nearest GpsPoint")
                                                            .anchor(0.5f, 0.5f)
                                                            .flat(true)
                                                            .icon(bitmapDescriptorFromVector(getContext(), R.drawable.gps_transperent_98)));


                                                } else { //update marker position

                                                    //Check three consecutive deviations to hit the API to get new route
                                                    double returnedDistance1 = 0.0;
                                                    double returnedDistance2 = 0.0;
                                                    double returnedDistance3 = 0.0;
                                                    if (consDistList != null && consDistList.size() > 2) {
                                                        returnedDistance1 = consDistList.get(consDistList.size() - 1);
                                                        //Log.e("APP DATA ", " Deviation Distance 1 ----" + returnedDistance1);
                                                        returnedDistance2 = consDistList.get(consDistList.size() - 2);
                                                        //Log.e("APP DATA ", "Deviation Distance 2 ----" + returnedDistance2);
                                                        returnedDistance3 = consDistList.get(consDistList.size() - 3);
                                                        //Log.e("APP DATA ", "Deviation Distance 3 ----" + returnedDistance3);
                                                    }

                                                    Log.e("ROUTE DEV MKR UPDATE", " WITHIN ROUTE DEIVATION MARKER UPDATE----" + currentGpsPosition + "," + currentPerpendicularPoint + "," + distance_movement);

                                                    //Get the deviated Route
                                                    if (returnedDistance1 > routeDeviationDistance
                                                            && returnedDistance2 > routeDeviationDistance
                                                            && returnedDistance3 > routeDeviationDistance) {
                                                        // Log.e("APP DATA ", "Route Deviated ----" + "YES.....");
                                                        //  Log.e("APP DATA ", " Deviation Distance 1 ----" + returnedDistance1);
                                                        //  Log.e("APP DATA ", " Deviation Distance 2 ----" + returnedDistance2);
                                                        //  Log.e("APP DATA ", " Deviation Distance 3 ----" + returnedDistance3);

                                                        Log.e("BEFR RT DEV HIT", " BEFORE ROUTE DEIVATION API HIT----" + currentGpsPosition + "," + currentPerpendicularPoint + "," + distance_movement);

                                                        // Log.e("APP DATA ", " OLD GPS ----" + OldGPSPosition);
                                                        Log.e("APP DATA ", " CGPS----" + currentGpsPosition);
                                                        //  Log.e("APP DATA ", " Per.OLD GPS----" + OldNearestPosition);
                                                        Log.e("APP DATA ", " Per.CGPS GPS-----" + currentPerpendicularPoint);

                                                        // No animation inside
                                                        //Hit API to get route and plot

                                                        verifyRouteDeviation(oldGPSPosition, currentGpsPosition, DestinationNode, routeDeviationDistance);
                                                        Log.e("APP DATA ", " oldGPSPosition ----" + oldGPSPosition);
                                                        //  Log.e("APP DATA ", " Per.OLD GPS----" + OldNearestPosition);
                                                        Log.e("APP DATA ", " currentGpsPosition -----" + currentGpsPosition);

                                                    }
                                                    if(mPositionMarker == null || mMap == null) {
                                                        return;
                                                    }
                                                    //map animation
                                                    Log.e("APP DATA ", " ANIMATE CAR MOVE oldGPSPosition-----" + oldGPSPosition);

                                                    Log.e("APP DATA ", "  ANIMATE CAR MOVE  currentGPSPosition-----" + currentGpsPosition);

                                                    animateCarMove(mPositionMarker, oldGPSPosition, currentGpsPosition, 1000);
                                                    float bearing = (float) bearingBetweenLocations(oldGPSPosition, currentGpsPosition);
                                                    Log.e("Fallow GPS ROUTE", "BEARING : " + bearing);
                                                    int height = 0;
                                                    if (getView() != null) {
                                                        height = getView().getMeasuredHeight();
                                                    }
                                                    Projection p = mMap.getProjection();
                                                    Point bottomRightPoint = p.toScreenLocation(p.getVisibleRegion().nearRight);
                                                    Point center = new Point(bottomRightPoint.x / 2, bottomRightPoint.y / 2);
                                                    Point offset = new Point(center.x, (center.y + (height / 4)));
                                                    LatLng centerLoc = p.fromScreenLocation(center);
                                                    Log.e("Fallow GPS ROUTE", "centerLoc : " + centerLoc.latitude + "," + centerLoc.longitude);
                                                    LatLng offsetNewLoc = p.fromScreenLocation(offset);
                                                    double offsetDistance = SphericalUtil.computeDistanceBetween(centerLoc, offsetNewLoc);
                                                    Log.e("Fallow GPS ROUTE", "offsetDistance : " + offsetDistance);
                                                    LatLng shadowTgt = SphericalUtil.computeOffset(currentGpsPosition, offsetDistance, bearing);
                                                    Log.e("Fallow GPS ROUTE", "shadowTgt : " + shadowTgt.latitude + "," + shadowTgt.longitude);
                                                    if (offsetDistance > 5 && bearing > 0.0) {
                                                        CameraPosition currentPlace_main = new CameraPosition.Builder()
                                                                .target(shadowTgt)
                                                                .bearing(bearing).tilt(65.5f).zoom(18)
                                                                .build();
                                                        mMap.animateCamera(CameraUpdateFactory.newCameraPosition(currentPlace_main), 1000, null);
                                                    }
                                                }
                                            }
                                        }

                                    }


                                    // Log.e("RECALL", "Re calling Location trigger method on 19 jan 2021 : " );

                                    //if the navigation is active then only make a recursive call
                                    if (isNavigationStarted && !isFragmentDestroyed) {
                                        tmpHandler.postDelayed(this, delay);
                                    } else {
                                        tmpHandler.removeCallbacksAndMessages(null);
                                        tmpHandler.removeCallbacks(this);
                                        if (myTimer != null) {
                                            myTimer.cancel();
                                            myTimer = null;
                                        }
                                    }
                                }
                            }, delay);
                        }
                        // }

                    } //end of Build version check
                }

                return 1;
            } catch (Exception e) {
                e.printStackTrace();
                Log.e("START NAVIGATION", e.getMessage(), e);
                return 0;
            }
        }
        //  }
        return 0;
    }

    @SuppressLint("MissingPermission")
    void saveLocation(LatLng location) {
        if (location != null) {
            lastGPSPosition = new LatLng(location.latitude, location.longitude);
        }
    }

    public int stopNavigation() {
            /*
              StopNavigation if user enables stop navigation
              show ALERT TYPE-5  for stoppping map
             */
        try {
//            islocationControlEnabled = true;
            if (SourceNode != null && DestinationNode != null) {
                if (mMap != null && isNavigationStarted) {
                    isNavigationStarted = false;
                    islocationControlEnabled = false;
                    //  Log.e("STOP NAVIGATION", "STOP NAVIGATION INNER VALUE --"+ islocationControlEnabled);


//                    if (mFusedLocationClient != null) {
//                        // mFusedLocationClient = null;
//                        mFusedLocationClient.removeLocationUpdates(locationCallback);
//                        //  Log.e("STOP NAVIGATION", "STOP NAVIGATION");
//                    }

                    if (currentGpsPosition != null) {
                        final Activity tmpActivity = getActivity();
                        if(tmpActivity != null) {
                            final Context context = tmpActivity.getApplicationContext();
                            if(context != null) {
                                String NavigationAlert = " Navigation Stopped " + currentGpsPosition;
                                sendData(MapEvents.ALERTVALUE_5, MapEvents.ALERTTYPE_5);

                                LayoutInflater inflater1 = tmpActivity.getLayoutInflater();
                                @SuppressLint("WrongViewCast") final View layout = inflater1.inflate(R.layout.custom_toast, (ViewGroup) getActivity().findViewById(R.id.textView_toast));
                                final TextView text = (TextView) layout.findViewById(R.id.textView_toast);
                                final ImageView image = (ImageView) layout.findViewById(R.id.image_toast);
                                Toast toast = new Toast(context);
                                String stopText = "Navigation Stopped";
                                text.setText(stopText);
                                if (stopText.startsWith("Navigation Stopped")) {
                                    image.setImageResource(R.drawable.stop_image);
                                }
                                toast.setDuration(Toast.LENGTH_LONG);
                                toast.setGravity(Gravity.TOP | Gravity.CENTER_HORIZONTAL, 0, 0);
                                toast.setGravity(Gravity.TOP, 0, 200);
                                toast.setView(layout);
                                toast.show();
                            }
                        }
                        // String NavigationAlert = " Navigation Stopped " ;

                    }
                    // getActivity().onBackPressed();
//                    islocationControlEnabled = false;
                    //  Log.e("STOP NAVIGATION", " islocationControlEnabled STOP NAVIGATION FLAG END VALUE "+ islocationControlEnabled);
                }
            }

            return 1;
        } catch (Exception e) {
            Log.e("STOP NAVIGATION", e.getMessage(), e);
            return 0;
        }
    }

    private void deinitialize(List<?> v) {
        return;
//        if(v != null) {
//            v.clear();
//        }
//        v = null;
    }

    @Override
    public void onDestroy() {
        Log.e("onDestroy", "NSGIMapFragmentActivity");


        deInitializeView();

        isFragmentDestroyed = true;

        myReceiver.releaseReference();
        myReceiver = null;

        asyncResponse = null;

//        lastGPSPosition = null;

//        oldGPSPosition = null;
        deinitialize(points);
        deinitialize(convertedPoints);



        deinitialize(currentRouteData);
        deinitialize(currentDeviatedRouteData);
        deinitialize(deviatedRouteData);

        deinitialize(nearestPointValuesList);
        deinitialize(OldNearestGpsList);
//        SourceNode = null;
//        DestinationNode = null;
//        currentGpsPosition = null;
        if (myTimer != null) {
            myTimer.cancel();
        }
        myTimer = null;
//        currentPerpendicularPoint = null;


        deinitialize(commonPoints);
        deinitialize(uncommonPoints);

        deinitialize(consDistList);

        deinitialize(destinationGeoFenceCoordinatesList);
        deinitialize(messageContainer);

        deinitialize(messageContainerTemp);

        currentPolylineOptions = null;
        currentPolylineGraphics = null;

        deviatedPolylineOptions = null;
        deviatedPolylineGraphics = null;

        deinitialize(edgeDataList);

//        nearlyFirstGPSPosition = null;

        locationUpdatesService = null;

        super.onDestroy();
    }


    @Override
    public void onDetach() {

        stopTTS();
        // Callback = null;
        super.onDetach();
    }

    public void SplitDestinationData(String destinationData) {
        destinationGeoFenceCoordinatesList = new ArrayList<LatLng>();
        String[] DestinationCordinates = destinationData.split(",");
        for (int p = 0; p < DestinationCordinates.length; p++) {
            // Log.e("DestinationData","Destination Data" + DestinationCordinates[p]);
            String dest_data = DestinationCordinates[p];
            String[] dest_latLngs = dest_data.split(" ");
            double dest_lat = Double.parseDouble(dest_latLngs[0]);
            double dest_lang = Double.parseDouble(dest_latLngs[1]);
            LatLng destinationLatLng = new LatLng(dest_lat, dest_lang);
            destinationGeoFenceCoordinatesList.add(destinationLatLng);

        }

    }


    public String displayNavigationMessage(final LatLng currentPosition) {

        String message = null;
        long distanceToTravel = 0l;

        LatLng perpendicularPoint = findNearestPointOnLine(currentRouteData, currentPosition);
        RouteMessage routeMessage = null;
        for (int i = 0; i < messageContainer.size(); i++) {
            routeMessage = messageContainer.get(i);
            if (PolyUtil.isLocationOnPath(perpendicularPoint, routeMessage.getLine(), false)) {
                break;
            }
        }

        if (routeMessage == null) {
            return message;
        }

        List<List<LatLng>> splittedLine = splitLineByPoint(routeMessage.getLine(), perpendicularPoint);

        if (splittedLine.size() == 2) {
            distanceToTravel = (long) SphericalUtil.computeLength(splittedLine.get(1));
            message = routeMessage.getMessage();
        }

        //for log only

        if (distanceToTravel == 0) {
            Log.e("routeMessage-", "currentRouteData: " + currentRouteData.toString());
            Log.e("routeMessage-", "currentPosition: " + currentPosition.toString());
            Log.e("routeMessage-", "perpendicularPoint: " + perpendicularPoint.toString());

            Log.e("routeMessage-", "message: " + routeMessage.getMessage());
            Log.e("routeMessage-", "line: " + routeMessage.getLine().toString());

            Log.e("routeMessage-", "splittedLine: " + splittedLine.toString());
        }


        if (message != null && !message.isEmpty() && distanceToTravel > 0) {
            String fullMessage = message + " " + distanceToTravel + " meters";
            if (getActivity() != null) {
                int speechStatus = textToSpeech.speak(fullMessage, TextToSpeech.QUEUE_FLUSH, null);
                if (speechStatus == TextToSpeech.ERROR) {
                    // Log.e("TTS", "Error in converting Text to Speech!");
                }

                LayoutInflater inflater1 = getActivity().getLayoutInflater();
                @SuppressLint("WrongViewCast") final View layout = inflater1.inflate(R.layout.custom_toast, (ViewGroup) getActivity().findViewById(R.id.textView_toast));
                TextView text = (TextView) layout.findViewById(R.id.textView_toast);

                text.setText(fullMessage);
                ImageView image = (ImageView) layout.findViewById(R.id.image_toast);
                if (message.contains("Take Right")) {
                    image.setImageResource(R.drawable.direction_right);
                } else if (message.contains("Take Left")) {
                    image.setImageResource(R.drawable.direction_left);
                }
                if (getActivity() != null) {
                    new Handler(Looper.getMainLooper()).post(new Runnable() {
                        @Override
                        public void run() {
                            final Activity tmpActivity = getActivity();
                            if (tmpActivity != null) {
                                final Context context = tmpActivity.getApplicationContext();
                                if(context != null) {
                                    Toast toast = new Toast(context);
                                    toast.setDuration(Toast.LENGTH_LONG);
                                    toast.setGravity(Gravity.TOP | Gravity.CENTER_HORIZONTAL, 0, 0);
                                    toast.setGravity(Gravity.TOP, 0, 130);
                                    toast.setView(layout);
                                    toast.show();
                                }
                            }

                        }
                    });
                }
            }
        }

        return message;
    }


    public void calculateETA(long startTimestamp, LatLng currentPosition, List<LatLng> routeLine) {

        if (routeLine.size() == 0 || startTimestamp == 0 || nearlyFirstGPSPosition == null) {
            return;
        }

        double vehicleSpeed = 0d;

        int timeTakenTillNow = (int) ((System.currentTimeMillis() - startTimestamp) / 1000); // in seconds

        double totalDistance = SphericalUtil.computeLength(routeLine);
//        int estimatedTime = (int) (((totalDistance / 1000) / vehicleSpeed) * 3600);   // in seconds
        List<List<LatLng>> splitRoute = splitLineByPoint(routeLine, currentPosition);

        int etaElapsed = 0;
        double remainingDistance = 0d;
        double minimumSpeed = (NSGIMapFragmentActivity.MINIMUM_VEHICLE_SPEED * 1000d) / 3600d;
        if (splitRoute.size() == 2) {
            remainingDistance = SphericalUtil.computeLength(splitRoute.get(1));
            double travelledDistance = SphericalUtil.computeLength(splitRoute.get(0));

            travelledDistance = travelledDistance - calculateDistanceAlongLineFromStart(splitRoute.get(0), nearlyFirstGPSPosition);

            if (timeTakenTillNow > 0 && travelledDistance > 0) {
                vehicleSpeed = travelledDistance / timeTakenTillNow;
            }

            if (vehicleSpeed > minimumSpeed) {
                estimatedRemainingTime = (int) (remainingDistance / vehicleSpeed);   // in seconds
            } else {
                estimatedRemainingTime = (int) (remainingDistance / minimumSpeed);   // in seconds
            }
        }

        if (timeTakenTillNow > estimatedTimeInSeconds) {
            etaElapsed = timeTakenTillNow - estimatedTimeInSeconds;
        }


//        time.append("Distance : ").append(totalDistance + " Meters ")
//                .append("::").append("total predicted time : ")
//                .append(estimatedTimeInSeconds + " SEC ")
//                .append("::").append(" Distance To Travel : ")
//                .append(estimatedRemainingTime + "Sec").append("::")
//                .append("Elapsed Time : ").append(etaElapsed).append("::")
//                .append("currentGpsPosition : ").append(currentPosition).append("\n");

        StringBuilder timeTmp = new StringBuilder();
        timeTmp.append("predicted time : ")
                .append(estimatedTimeInSeconds + " SEC ").append("::")
                .append("Elapsed time: ").append(etaElapsed).append("::")
                .append("timeTakenTillNow: ").append(timeTakenTillNow).append("::")
                .append("estimatedRemainingTime: ").append(estimatedRemainingTime).append("::")
                .append("totalDistance: ").append(totalDistance).append("::")
                .append("remainingDistance: ").append(remainingDistance).append("::")
                .append("vehicleSpeed (mtr./sec): ").append(vehicleSpeed).append("::");
        if (vehicleSpeed > minimumSpeed) {
            timeTmp.append("used vehicleSpeed (mtr./sec): ").append(vehicleSpeed).append("::");
        } else {
            timeTmp.append("used vehicleSpeed (mtr./sec): ").append(minimumSpeed).append("::");
        }
        timeTmp.append("currentGpsPosition : ").append(currentPosition.toString()).append("\n");


        Log.e("ETA", "ETA ALERT ---- " + timeTmp);

        Log.e("ETA", "currentPosition ---- " + reverseCoordinate(currentPosition).toString());
        Log.e("ETA", "routeLine ---- " + reverseCoordinates(routeLine).toString());

        for (List<LatLng> elem : splitRoute) {
            Log.e("ETA", "splitRoute ---- " + reverseCoordinates(elem).toString());
        }
        Log.e("ETA", "vehicleSpeed ---- " + vehicleSpeed);
        Log.e("ETA", "timeTakenTillNow ---- " + timeTakenTillNow);

        sendData(timeTmp.toString(), MapEvents.ALERTTYPE_2);

        if (etaElapsed > 0 && !isETACrossed) {
            // send eta message only one time
            isETACrossed = true;
            sendData(timeTmp.toString(), MapEvents.ALERTTYPE_7);
        }

    }


    //@RequiresApi(api = Build.VERSION_CODES.JELLY_BEAN)


    @RequiresApi(api = Build.VERSION_CODES.JELLY_BEAN)
    public void verifyRouteDeviation(final LatLng previousGpsPosition,
                                     final LatLng currentGpsPosition,
                                     final LatLng destinationPosition,
                                     int markDistance) {

        if (routeAPIHit == true) return;

               /*
              After getting current gps verifing in the  radius of
              in the routebetween the Previous and current gps position
              if Route deviation exists it shows the message Route Deviated it will get route from the service and plot route on map
               otherwise continue with the existed route
              */
        Log.e("Route Deviation", "CURRENT GPS ----" + currentGpsPosition);
        Log.e("Route Deviation", " OLD GPS POSITION  ----" + previousGpsPosition);

        List<LatLng> currentRouteDataLocal = new ArrayList<>();

        if (previousGpsPosition != null) {

            LatLng nearest_LatLng_deviation = findNearestPointOnLine(currentRouteData, currentGpsPosition);
            //findNearestPointOnLine
            double returnedDistance = showDistance(currentGpsPosition, nearest_LatLng_deviation);
            //Log.e("Route Deviation","ROUTE DEVIATION DISTANCE RETURNED ---- "+returnedDistance);
            if (returnedDistance > routeDeviationDistance) {

                String cgpsLat = String.valueOf(currentGpsPosition.latitude);
                String cgpsLongi = String.valueOf(currentGpsPosition.longitude);
                final String routeDiationPosition = cgpsLongi.concat(" ").concat(cgpsLat);
                // Log.e("Route Deviation", "routeDiationPosition   ######" + routeDiationPosition);

                String destLatPos = String.valueOf(destinationPosition.latitude);
                String destLongiPos = String.valueOf(destinationPosition.longitude);
                final String destPoint = destLongiPos.concat(" ").concat(destLatPos);

                LatLng routeDeviatedSourcePosition = cloneCoordinate(currentGpsPosition);
                Log.e("Route Deviation", "routeDiation SOURCE Position  ###### " + routeDeviatedSourcePosition);
                // Log.e("returnedDistance", "RouteDiationPosition  ###### " + routeDiationPosition);
                //   Log.e("returnedDistance", "Destination Position --------- " + destPoint);
                //  DestinationPosition = new LatLng(destLat, destLng);
                if (getActivity() != null) {

                    routeAPIHit = true;
                    if (asyncResponse == null) {
                        asyncResponse = new AsyncResponse() {
                            @Override
                            public void processFinish(Object output) {

                                try {

                                    // initialize global variables and save data to DB
                                    getRouteDetails((String) output);

                                    //COMPARE OLD AND NEW ROUTES - MAKE FINAL ROUTE

                                    //PLOT ON MAP

                                    //DISPLAY ROUTE DEVIATION MESSAGE AND VOICE ALERT

                                    //FOLLOW NEW ROUTE FOR FURTHER DEVIATIONS

                                    Log.e("ROUTE DEV MKR UPDATE", " WITHIN ROUTE API HIT----");

                                    if (currentDeviatedRouteData != null && currentDeviatedRouteData.size() > 0) {

                                        Log.e("ROUTE DEV MKR UPDATE", " AFTER RECVD DATA FROM API----");

                                        //original routes - eliminating duplicate coordinates in line segments
                                        currentRouteDataLocal.addAll(cloneCoordinates(currentRouteData));

                                        // List<LatLng> currentRouteDataLocal = removeDuplicatesRouteDeviated(RouteDeviationPointsForComparision);
                                        Log.e("DESTINATION POSITION", "DESTINATION POSITION" + DestinationNode);
                                        Log.e("ROUTE DEV MKR UPDATE", "BEFORE VERIFICATION OF OLD AND NEW ROUTE");
                                        //Issue here may be
                                        compareDeviatedRouteWithCurrentRoute(currentRouteDataLocal, currentDeviatedRouteData);

                                        Log.e("List Verification", "List Verification commonPoints --  DATA " + commonPoints.size());
                                        Log.e("List Verification", "List Verification  new_unCommonPoints -- DATA " + uncommonPoints.size());

                                        Log.e("ROUTE DEV MKR UPDATE", "BEFORE PLOTTING DEVIATED ROUTE");

                                        Log.e("ROUTE DEV MKR UPDATE", "BEFORE PLOTTING DEVIATED ROUTE, UNCOMMON POINTS SIZE:" + uncommonPoints.size());

                                        if (uncommonPoints.size() > 1) {

                                            //  Log.e("Route Deviation", " IS ROUTE VERIFY  ###### " + " Route COINSIDENCE");
                                            List<LatLng> tmpVar = mergeRoutes(currentRouteDataLocal, currentDeviatedRouteData, routeDeviatedSourcePosition);
                                            currentRouteData.clear();
                                            currentRouteData.addAll(tmpVar);

                                            //refresh the message container with the new one as the route is deviated
                                            messageContainer.clear();
                                            messageContainer.addAll(messageContainerTemp);

                                            if (deviatedRouteData.size() == 0) {
                                                // adding the perpendicular point to start,  for the first deviation
                                                currentDeviatedRouteData.add(0, nearest_LatLng_deviation);
                                            }

                                            //add the deviated route
                                            tmpVar = mergeRoutes(deviatedRouteData, currentDeviatedRouteData, routeDeviatedSourcePosition);
                                            deviatedRouteData.clear();
                                            deviatedRouteData.addAll(tmpVar);

                                            //Plotting uncommon points as a line here
                                            if (mPositionMarker != null && mPositionMarker.isVisible()) {

                                                if (deviatedRouteData.size() > 1) {
                                                    if (deviatedPolylineGraphics == null) {
                                                        deviatedPolylineOptions.addAll(cloneCoordinates(deviatedRouteData));
                                                        deviatedPolylineOptions.color(NSGIMapFragmentActivity.DEVIATED_ROUTE_COLOR).width(NSGIMapFragmentActivity.DEVIATED_ROUTE_WIDTH);
                                                        deviatedPolylineGraphics = mMap.addPolyline(deviatedPolylineOptions);
                                                    } else {
                                                        deviatedPolylineGraphics.setPoints(cloneCoordinates(deviatedRouteData));
                                                        deviatedPolylineGraphics.setColor(NSGIMapFragmentActivity.DEVIATED_ROUTE_COLOR);
                                                        deviatedPolylineGraphics.setWidth(NSGIMapFragmentActivity.DEVIATED_ROUTE_WIDTH);
                                                    }
                                                }

                                                Log.e("ROUTE DEV MKR UPDATE", "DEVIATED ROUTE PLOTTED");
                                                // isContinuoslyOutOfTrack = true;
                                                if (getActivity() != null) {
                                                    Log.e("START OF DEV MSG LOG", "ENTERED INTO DEVIATION MSG LOG");
                                                    Log.e("ROUTE DEV MKR UPDATE", "RAISE TOAST MESSAGE ONLY ONCE");
                                                    LayoutInflater inflater1 = getActivity().getLayoutInflater();
                                                    @SuppressLint("WrongViewCast") View layout = inflater1.inflate(R.layout.custom_toast, (ViewGroup) getActivity().findViewById(R.id.textView_toast));
                                                    TextView text = (TextView) layout.findViewById(R.id.textView_toast);
                                                    text.setText(" ROUTE DEVIATED ");
                                                    // set image deviated
                                                    final ImageView image = (ImageView) layout.findViewById(R.id.image_toast);
                                                    String deviatedText = " ROUTE DEVIATED ";
                                                    if (deviatedText.startsWith(" ROUTE DEVIATED ")) {
                                                        image.setImageResource(R.drawable.deviate_64);
                                                    }
                                                    //set image deviated
                                                    final Activity tmpActivity = getActivity();
                                                    if(tmpActivity != null) {
                                                        final Context context = tmpActivity.getApplicationContext();
                                                        if(context != null) {
                                                            Toast toast = new Toast(context);
                                                            toast.setDuration(Toast.LENGTH_LONG);
                                                            toast.setGravity(Gravity.TOP | Gravity.CENTER_HORIZONTAL, 0, 0);
                                                            toast.setGravity(Gravity.TOP, 0, 150);
                                                            toast.setView(layout);
                                                            toast.show();
                                                        }
                                                    }

                                                    StringBuilder routeDeviatedAlert = new StringBuilder();
                                                    routeDeviatedAlert.append("ROUTE DEVIATED" + " RouteDeviatedSourcePosition : " + routeDeviatedSourcePosition);
                                                    sendData(MapEvents.ALERTVALUE_3, MapEvents.ALERTTYPE_3);
                                                    Log.e("Route Deviation", " Route Deviation Alert POSTED" + MapEvents.ALERTVALUE_3);
                                                    Log.e(" END OF DEV MSG LOG", "ENTERED INTO DEVIATION MSG LOG");
                                                    alertDestination(currentGpsPosition);
                                                    // added on 25-04-20 by SKC
                                                    int timeTakenTillNow = (int) (System.currentTimeMillis() - startTimestamp) / 1000;
                                                    if (timeTakenTillNow >= 5) {
                                                        calculateETA(startTimestamp, currentGpsPosition, currentRouteData);
                                                    }
                                                }
                                            }
                                        }

                                    }
                                } catch (Exception ex) {
                                    Log.e("VerifyRoute", "VerifyRoute error", ex);
                                } finally {
                                    routeAPIHit = false;
                                }
                            }
                        };
                    }

                    DownloadRouteFromURL download = new DownloadRouteFromURL(asyncResponse, routeDeviatedDT_URL, AuthorisationKey);
                    download.execute(routeDiationPosition, destPoint);
                }
            }
        }
    }


    public void compareDeviatedRouteWithCurrentRoute(List<LatLng> currentRoute, List<LatLng> deviatedRoute) {

        commonPoints.clear();
        uncommonPoints.clear();

        if (currentRoute.size() == 0) {
            uncommonPoints.addAll(cloneCoordinates(deviatedRoute));
            return;
        }

        for (int i = 0; i < deviatedRoute.size(); i++) {
            LatLng deviatedRoutePoint = deviatedRoute.get(i);
            Log.e("DEVIATION COMPARISION", "DEVIATION COMPARISION BEFORE TRUNCATED NEW " + deviatedRoutePoint);

            if (PolyUtil.isLocationOnPath(deviatedRoutePoint, currentRoute, false)) {
                commonPoints.add(cloneCoordinate(deviatedRoutePoint));
            } else {
                uncommonPoints.add(cloneCoordinate(deviatedRoutePoint));
                Log.e("DESTINATION POSITION", "DESTINATION POSITION" + DestinationNode);
            }

//            boolean innerFlag = false;
//            for (int j = 0; j < currentRoute.size(); j++) {
//                LatLng oldRoutePoint = currentRoute.get(j);
//                Log.e("DEVIATION COMPARISION", "DEVIATION COMPARISION BEFORE TRUNCATED OLD " + oldRoutePoint);
//
//
//
//                if (isSameCoordinate(deviatedRoutePoint, oldRoutePoint)) {
//                    commonPoints.add(cloneCoordinate(oldRoutePoint));
//                    innerFlag = true;
//                }
//
//            }
//            if (!innerFlag) {
//                uncommonPoints.add(cloneCoordinate(deviatedRoutePoint));
//                Log.e("DESTINATION POSITION", "DESTINATION POSITION" + DestinationNode);
//            }
        }
        Log.e("COMMON AND UNCOMMON", "SIZES, common:" + commonPoints.size() + "Uncommon" + uncommonPoints.size());

    }


    private void getRouteDetails(String FeatureResponse) {
        JSONObject jsonObject = null;
        try {
            if (FeatureResponse != null) {
                jsonObject = new JSONObject(FeatureResponse);
                // String ID = String.valueOf(jsonObject.get("$id"));

                // String Status = jsonObject.getString("Status");
                double TotalDistance = jsonObject.getDouble("TotalDistance");

                JSONArray jSonRoutes = new JSONArray(jsonObject.getString("Route"));

                currentDeviatedRouteData.clear();
                messageContainerTemp.clear();

                for (int i = 0; i < jSonRoutes.length(); i++) {
                    List deviationPoints = new ArrayList();
                    List<LatLng> arrayOfCoordinates = new ArrayList<>();

                    JSONObject Routes = new JSONObject(jSonRoutes.get(i).toString());

//                    String EdgeNo = Routes.getString("EdgeNo");
                    String GeometryText = Routes.getString("GeometryText");
                    JSONObject geometryObject = new JSONObject(Routes.getString("Geometry"));
                    JSONArray jSonLegs = new JSONArray(geometryObject.getString("coordinates"));
                    for (int j = 0; j < jSonLegs.length(); j++) {
                        deviationPoints.add(jSonLegs.get(j));
                    }

                    //converting the first point to LatLng object
                    String stPoint = String.valueOf(jSonLegs.get(0));
                    stPoint = stPoint.replace("[", "");
                    stPoint = stPoint.replace("]", "");

                    for (int p = 0; p < deviationPoints.size(); p++) {

                        String listItem = deviationPoints.get(p).toString();
                        listItem = listItem.replace("[", "");
                        listItem = listItem.replace("]", "");
                        String[] subListItem = listItem.split(",");
                        double y = Double.parseDouble(subListItem[0]);
                        double x = Double.parseDouble(subListItem[1]);

                        arrayOfCoordinates.add(new LatLng(x, y));
                    }

                    currentDeviatedRouteData.addAll(cloneCoordinates(arrayOfCoordinates));

                    messageContainerTemp.add(new RouteMessage(GeometryText, arrayOfCoordinates));
                }
                removeDuplicatesRouteDeviated(currentDeviatedRouteData);
            }
        } catch (JSONException e) {
            e.printStackTrace();
            Log.e("GetRouteDetails ", Objects.requireNonNull(e.getMessage()), e);
        }

    }


    public static void animateMarker(final LatLng startPosition, final LatLng destination, final Marker marker) {
        if (marker != null) {
            // final LatLng startPosition = marker.getPosition();
            final LatLng endPosition = new LatLng(destination.latitude, destination.longitude);

            final float startRotation = marker.getRotation();

            final LatLngInterpolator latLngInterpolator = new LatLngInterpolator.LinearFixed();
            ValueAnimator valueAnimator = ValueAnimator.ofFloat(0, 1);
            valueAnimator.setDuration(2000); // duration 1 second
            valueAnimator.setInterpolator(new LinearInterpolator());
            valueAnimator.addUpdateListener(new ValueAnimator.AnimatorUpdateListener() {
                @Override
                public void onAnimationUpdate(ValueAnimator animation) {
                    try {
                        float v = animation.getAnimatedFraction();
                        float bearing = (float) getAngle(startPosition, destination);
                        LatLng newPosition = latLngInterpolator.interpolate(v, startPosition, endPosition);
                        marker.setPosition(newPosition);
                        marker.setRotation(bearing);
                    } catch (Exception e) {
                        // I don't care atm..
                        Log.e("animateMarker", e.getMessage(), e);
                    }
                }
            });

            valueAnimator.start();
        }
    }

    private void drawMarkerWithCircle(LatLng gpsPosition, double radius) {
        CircleOptions circleOptions = new CircleOptions().center(gpsPosition).radius(radius).fillColor(Color.parseColor("#2271cce7")).strokeColor(Color.parseColor("#2271cce7")).strokeWidth(3);
        mCircle = mMap.addCircle(circleOptions);

    }


    public void alertDestination(LatLng currentGpsPosition) {

        if (destinationGeoFenceCoordinatesList != null && destinationGeoFenceCoordinatesList.size() > 2) {
            //PolygonOptions polygonOptions = new PolygonOptions().addAll(destinationGeoFenceCoordinatesList);
            //mMap.addPolygon(polygonOptions);
            //polygonOptions.fillColor(Color.CYAN);
            isLieInGeofence = false;
            isLieInGeofence = pointWithinPolygon(currentGpsPosition, destinationGeoFenceCoordinatesList);
            Log.e("Destination Geofence", "Destination Geofence Cordinates : " + destinationGeoFenceCoordinatesList);

            Log.e("Destination Geofence", "Destination Geofence : " + isLieInGeofence);
            if (getActivity() != null) {
                if (isAlertShown == false) {

                    if (isLieInGeofence == true) {

                        String data1 = " Your Destination Reached ";
                        int speechStatus1 = textToSpeech.speak(data1, TextToSpeech.QUEUE_FLUSH, null);
                        if (speechStatus1 == TextToSpeech.ERROR) {
                            Log.e("TTS", "Error in converting Text to Speech!");
                        }
                        sendData(MapEvents.ALERTVALUE_4, MapEvents.ALERTTYPE_4);

                        Log.e("AlertDestination", "Alert Destination" + "DESTINATION REACHED--");
                        isAlertShown = true;
                        //added by SKC
                        isNavigationStarted = false;

                        //need to clear resources

                    } else {
                        //Log.e("AlertDestination", "Alert Destination" + "DESTINATION NOT REACHED--");
                    }
                } else {

                }
            }
        } //end of If
    }


    private void sendData(String comm, int AlertType) {

        FragmentToActivity callback = (FragmentToActivity) getActivity();

        if (callback != null) {
            //comm=time.toString();
            if (comm != null) {
                //  Log.e("SendData", "SendData ------- " + comm + "AlertType" + AlertType);
                callback.communicate(comm, AlertType);
            } else {

            }
        }


    }


    public void addMarkers() {
        if (SourceNode != null && DestinationNode != null) {
            sourceMarker = mMap.addMarker(new MarkerOptions()
                    .position(SourceNode)
                    .icon(bitmapDescriptorFromVector(getActivity(), R.drawable.source_marker_whitetext)));
            CameraPosition googlePlex = CameraPosition.builder()
                    .target(SourceNode)
                    .zoom(18)
                    .tilt(45)
                    .build();
            mMap.animateCamera(CameraUpdateFactory.newCameraPosition(googlePlex), 1000, null);

            destinationMarker = mMap.addMarker(new MarkerOptions()
                    .position(DestinationNode)
                    .icon(bitmapDescriptorFromVector(getActivity(), R.drawable.destination_marker_whitetext_lightgreen)));
            Log.e("Source Marker ", "SourceNode Marker : " + SourceNode);
            Log.e("Destination Marker", "DestinationNode Marker : " + DestinationNode);

               /*
                CameraPosition googlePlex1 = CameraPosition.builder()
                        .target(DestinationNode)
                        .zoom(18)
                        .tilt(45)
                        .build();

                mMap.animateCamera(CameraUpdateFactory.newCameraPosition(googlePlex1), 1000, null);

                */
        } else {
            mMap.addMarker(new MarkerOptions()
                    .position(new LatLng(24.984408, 55.072814))
                    .icon(bitmapDescriptorFromVector(getActivity(), R.drawable.blue_marker)));
            CameraPosition googlePlex = CameraPosition.builder()
                    .target(new LatLng(24.984408, 55.072814))
                    .zoom(15)
                    .tilt(45)
                    .build();
            mMap.animateCamera(CameraUpdateFactory.newCameraPosition(googlePlex), 1000, null);

        }
    }

    /**
     * Saving first route data to DB
     *
     * @param FeatureResponse
     */
    public void GetRouteFromDBPlotOnMap(String FeatureResponse) {
        String delQuery = "DELETE  FROM " + EdgeDataT.TABLE_NAME;
        // sqlHandler.executeQuery(delQuery);
        JSONObject jsonObject = null;
        try {
            if (FeatureResponse != null) {
                jsonObject = new JSONObject(FeatureResponse);
                String ID = String.valueOf(jsonObject.get("$id"));
                String Status = jsonObject.getString("Status");
                double TotalDistance = jsonObject.getDouble("TotalDistance");
                TotalDistanceInMTS = TotalDistance * 100000;
                JSONArray jSonRoutes = new JSONArray(jsonObject.getString("Route"));
//                PolylineOptions polylineOptions = new PolylineOptions();
                convertedPoints = new ArrayList<LatLng>();

                if (jSonRoutes.length() > 0) {
                    messageContainer.clear();
                    currentRouteData.clear();
                }

                for (int i = 0; i < jSonRoutes.length(); i++) {
                    points = new ArrayList();

                    List<LatLng> arrayOfCoordinates = new ArrayList<>();

                    JSONObject Routes = new JSONObject(jSonRoutes.get(i).toString());
                    String $id = Routes.getString("$id");
                    String EdgeNo = Routes.getString("EdgeNo");
                    String GeometryText = Routes.getString("GeometryText");
                    String Geometry = Routes.getString("Geometry");
                    JSONObject geometryObject = new JSONObject(Routes.getString("Geometry"));
                    String $id1 = geometryObject.getString("$id");
                    String type = geometryObject.getString("type");
                    String coordinates = geometryObject.getString("coordinates");
                    JSONArray jSonLegs = new JSONArray(geometryObject.getString("coordinates"));
                    for (int j = 0; j < jSonLegs.length(); j++) {
                        points.add(jSonLegs.get(j));
                    }

                    String stPoint = String.valueOf(jSonLegs.get(0));
                    String endPoint = String.valueOf(jSonLegs.get(jSonLegs.length() - 1));

                    stPoint = stPoint.replace("[", "");
                    stPoint = stPoint.replace("]", "");
                    String[] firstPoint = stPoint.split(",");
                    Double stPointLat = Double.valueOf(firstPoint[0]);
                    Double stPointLongi = Double.valueOf(firstPoint[1]);
                    LatLng stVertex = new LatLng(stPointLongi, stPointLat);

                    endPoint = endPoint.replace("[", "");
                    endPoint = endPoint.replace("]", "");
                    String[] secondPoint = endPoint.split(",");
                    Double endPointLat = Double.valueOf(secondPoint[0]);
                    Double endPointLongi = Double.valueOf(secondPoint[1]);
                    LatLng endVertex = new LatLng(endPointLongi, endPointLat);


                    double distance = showDistance(stVertex, endVertex);
                    String distanceInKM = String.valueOf(distance / 1000);
                    StringBuilder query = new StringBuilder("INSERT INTO ");
                    query.append(EdgeDataT.TABLE_NAME).append("(edgeNo,distanceInVertex,startPoint,allPoints,geometryText,endPoint) values (")
                            .append("'").append(EdgeNo).append("',")
                            .append("'").append(distanceInKM).append("',")
                            // .append("'").append(String.valueOf(TotalDistanceInMTS)).append("',")
                            .append("'").append(jSonLegs.get(0)).append("',")
                            .append("'").append(points).append("',")
                            .append("'").append(GeometryText).append("',")
                            .append("'").append(jSonLegs.get(jSonLegs.length() - 1)).append("')");
                    //sqlHandler.executeQuery(query.toString());
                    //sqlHandler.closeDataBaseConnection();

                    for (int p = 0; p < points.size(); p++) {
                        String listItem = points.get(p).toString();
                        listItem = listItem.replace("[", "");
                        listItem = listItem.replace("]", "");
                        String[] subListItem = listItem.split(",");
                        Double y = Double.valueOf(subListItem[0]);
                        Double x = Double.valueOf(subListItem[1]);
                        StringBuilder sb = new StringBuilder();
                        LatLng latLng = new LatLng(x, y);
                        convertedPoints.add(latLng);

                        arrayOfCoordinates.add(new LatLng(x, y));
                    }
                    Log.e("convertedPoints", " convertedPoints------ " + convertedPoints.size());

                    // 55.065312867000046, 24.977084458000036
//                    MarkerOptions markerOptions = new MarkerOptions();
//                    for (int k = 0; k < convertedPoints.size(); k++) {
//                        if (polylineOptions != null && mMap != null) {
//                            markerOptions.position(convertedPoints.get(k));
//                            markerOptions.title("Position");
//                        }
//                    }

                    currentRouteData.addAll(cloneCoordinates(arrayOfCoordinates));
                    //add message
                    messageContainer.add(new RouteMessage(GeometryText, arrayOfCoordinates));
                }

                // will remove the duplicates remove that object
                removeDuplicatesRouteDeviated(currentRouteData);

                SourceNode = cloneCoordinate(currentRouteData.get(0));
                DestinationNode = cloneCoordinate(currentRouteData.get(currentRouteData.size() - 1));

                // DRAWING THE CURRENT ROUTE
                currentPolylineOptions.addAll(cloneCoordinates(convertedPoints));
                currentPolylineOptions.color(NSGIMapFragmentActivity.CURRENT_ROUTE_COLOR).width(NSGIMapFragmentActivity.CURRENT_ROUTE_WIDTH);
                currentPolylineGraphics = mMap.addPolyline(currentPolylineOptions);
                // polyline.setJointType(JointType.ROUND);
            }
        } catch (JSONException e) {
            Log.e("GetRouteFromDBPlotOnMap", e.getMessage(), e);
            e.printStackTrace();
        }

    }

    private boolean checkPermission() {
        return PackageManager.PERMISSION_GRANTED == ContextCompat.checkSelfPermission(getContext(), ACCESS_FINE_LOCATION) &&
                PackageManager.PERMISSION_GRANTED == ContextCompat.checkSelfPermission(getContext(), READ_EXTERNAL_STORAGE);
    }

    private void requestPermission() {

        ActivityCompat.requestPermissions(getActivity(), new String[]{ACCESS_FINE_LOCATION, READ_EXTERNAL_STORAGE}, PERMISSION_REQUEST_CODE);

    }


    @Override
    public void onRequestPermissionsResult(int requestCode, @NonNull String[] permissions, @NonNull int[] grantResults) {
        super.onRequestPermissionsResult(requestCode, permissions, grantResults);
        switch (requestCode) {
            case PERMISSION_REQUEST_CODE: {
                if (grantResults.length > 0) {

                    locationAccepted = grantResults[0] == PackageManager.PERMISSION_GRANTED;
                    boolean storageAccepted = grantResults[1] == PackageManager.PERMISSION_GRANTED;

                    if (locationAccepted && storageAccepted) {
                        Toast.makeText(getContext(), "Permission Granted,.", Toast.LENGTH_LONG).show();
                    } else {
                        // Toast.makeText(this, "Permission Denied, You cannot access location data and camera.", Snackbar.LENGTH_LONG).show();

                        if (Build.VERSION.SDK_INT >= Build.VERSION_CODES.M) {
                            if (shouldShowRequestPermissionRationale(ACCESS_FINE_LOCATION)) {
                                AlertDialog.Builder builder = new AlertDialog.Builder(getContext());
                                builder.setMessage("Look at this dialog!")
                                        .setCancelable(false)
                                        .setPositiveButton("OK", new DialogInterface.OnClickListener() {
                                            public void onClick(DialogInterface dialog, int id) {
                                                if (Build.VERSION.SDK_INT >= Build.VERSION_CODES.M) {
                                                    requestPermissions(new String[]{ACCESS_FINE_LOCATION, READ_EXTERNAL_STORAGE},
                                                            PERMISSION_REQUEST_CODE);
                                                }
                                            }
                                        });
                                AlertDialog alert = builder.create();
                                alert.show();

                                return;
                            }
                        }

                    }
                }
            }
            break;
            case 1000: {
                // If request is cancelled, the result arrays are empty.
                if (grantResults.length > 0
                        && grantResults[0] == PackageManager.PERMISSION_GRANTED) {

                    //startLocationUpdates();
                    /*if (isContinue) {
                        mFusedLocationClient.requestLocationUpdates(locationRequest, locationCallback, null);
                    } else {
                        mFusedLocationClient.getLastLocation().addOnSuccessListener(getActivity(), new OnSuccessListener<Location>() {
                            @Override
                            public void onSuccess(Location location) {
                                if (location != null) {
                                    wayLatitude = location.getLatitude();
                                    wayLongitude = location.getLongitude();
                                    // Log.v("APP DATA","LAT VALUE"+wayLatitude);
                                    // Log.v("APP DATA","LAT VALUE"+wayLongitude);
                                    //txtLocation.setText(String.format(Locale.US, "%s - %s", wayLatitude, wayLongitude));


                                } else {
                                    mFusedLocationClient.requestLocationUpdates(locationRequest, locationCallback, null);
                                }
                            }
                        });
                    }*/
                } else {
                    Toast.makeText(getContext(), "Permission denied", Toast.LENGTH_SHORT).show();
                }
                break;
            }
        }
    }


    @Override
    public void onActivityResult(int requestCode, int resultCode, Intent data) {
        super.onActivityResult(requestCode, resultCode, data);
        if (resultCode == Activity.RESULT_OK) {
            if (requestCode == AppConstants.GPS_REQUEST) {
//                isGPS = true; // flag maintain before get location
            }
        }
    }

    private void animateCarMove(final Marker marker, final LatLng beginLatLng, final LatLng endLatLng, final long duration) {

//        if(animateCarMoveHandler == null) {
//            animateCarMoveHandler = new Handler();
//        }
        final Handler tmpHandler = new Handler(Looper.getMainLooper());

        final long startTime = SystemClock.uptimeMillis();
        final Interpolator interpolator = new LinearInterpolator();
        // set car bearing for current part of path

//        float angleDeg = (float) (180 * Utils.getAngle(beginLatLng, endLatLng) / Math.PI);
//        Matrix matrix = new Matrix();
//        matrix.postRotate(angleDeg);
        // marker.setIcon(BitmapDescriptorFactory.fromBitmap(Bitmap.createBitmap(mMarkerIcon, 0, 0,mMarkerIcon.getWidth(), mMarkerIcon.getHeight(), matrix, true)));
        //marker.setIcon(BitmapDescriptorFactory.fromBitmap(Bitmap.createBitmap(mMarkerIcon, 0, 0, centerX,centerY, matrix, true)));
//        if (animateCarMoveRunnable == null) {
//            animateCarMoveRunnable = ;
//        }

        tmpHandler.post(new Runnable() {
            @RequiresApi(api = Build.VERSION_CODES.JELLY_BEAN)
            @Override
            public void run() {

                if (isLieInGeofence || isFragmentDestroyed) {
                    Log.e("Animate marker", "Animate marker destination alert in if " + isLieInGeofence);
                    tmpHandler.removeCallbacksAndMessages(null);
                    tmpHandler.removeCallbacks(this);
                } else if(marker != null && beginLatLng != null && endLatLng != null) {
                    Log.e("Animate marker", "Animate marker destination alert in else" + isLieInGeofence);

                    // calculate phase of animation
                    long elapsed = SystemClock.uptimeMillis() - startTime;
                    float t = interpolator.getInterpolation((float) elapsed / duration);
                    // calculate new position for marker
                    double lat = (endLatLng.latitude - beginLatLng.latitude) * t + beginLatLng.latitude;
                    double lngDelta = endLatLng.longitude - beginLatLng.longitude;
                    if (Math.abs(lngDelta) > 180) {
                        lngDelta -= Math.signum(lngDelta) * 360;
                    }
                    Location location = new Location(LocationManager.GPS_PROVIDER);
                    location.setLatitude(endLatLng.latitude);
                    location.setLongitude(endLatLng.longitude);
                    float bearingMap = location.getBearing();
                    //  float bearingMap= mMap.getCameraPosition().bearing;
                    float bearing = (float) Utils.bearingBetweenLocations(beginLatLng, endLatLng);
                    float angle = -azimuthInDegress + bearing;
                    float rotation = -azimuthInDegress * 360 / (2 * 3.14159f);
                    double lng = lngDelta * t + beginLatLng.longitude;
                    marker.setPosition(new LatLng(lat, lng));
                    marker.setAnchor(0.5f, 0.5f);
                    marker.setFlat(true);
                    if (bearing > 0.0) {
                        marker.setRotation(bearing);
                    }
                    if (t < 1.0) {
                        tmpHandler.postDelayed(this, 16);
                    }
                }
            }
        });
    }

    private void animateCarMoveNotUpdateMarker(final Marker marker, final LatLng beginLatLng, final LatLng endLatLng, final long duration) {
//        if(animateCarMoveNotUpdateMarkerHandler == null) {
//            animateCarMoveNotUpdateMarkerHandler = new Handler();
//        }
        final Handler tmpHandler = new Handler();
        final long startTime = SystemClock.uptimeMillis();
        final Interpolator interpolator = new LinearInterpolator();
        // set car bearing for current part of path
        float angleDeg = (float) (180 * Utils.getAngle(beginLatLng, endLatLng) / Math.PI);
        Matrix matrix = new Matrix();
        matrix.postRotate(angleDeg);
        // marker.setIcon(BitmapDescriptorFactory.fromBitmap(Bitmap.createBitmap(mMarkerIcon, 0, 0,mMarkerIcon.getWidth(), mMarkerIcon.getHeight(), matrix, true)));
        //marker.setIcon(BitmapDescriptorFactory.fromBitmap(Bitmap.createBitmap(mMarkerIcon, 0, 0, centerX,centerY, matrix, true)));
        if (animateCarMoveNotUpdateMarkerRunnable == null) {
            animateCarMoveNotUpdateMarkerRunnable = new Runnable() {
                @RequiresApi(api = Build.VERSION_CODES.JELLY_BEAN)
                @Override
                public void run() {

                    if (isLieInGeofence || isFragmentDestroyed) {
                        Log.e("Animate marker", "Animate marker destination alert in if " + isLieInGeofence);
                        tmpHandler.removeCallbacks(this);
                    } else {
                        Log.e("Animate marker", "Animate marker destination alert in else" + isLieInGeofence);
                    }

                    // calculate phase of animation
                    long elapsed = SystemClock.uptimeMillis() - startTime;
                    float t = interpolator.getInterpolation((float) elapsed / duration);
                    // calculate new position for marker
                    double lat = (endLatLng.latitude - beginLatLng.latitude) * t + beginLatLng.latitude;
                    double lngDelta = endLatLng.longitude - beginLatLng.longitude;
                    if (Math.abs(lngDelta) > 180) {
                        lngDelta -= Math.signum(lngDelta) * 360;
                    }
                    Location location = new Location(LocationManager.GPS_PROVIDER);
                    location.setLatitude(endLatLng.latitude);
                    location.setLongitude(endLatLng.longitude);
                    float bearingMap = location.getBearing();
                    //  float bearingMap= mMap.getCameraPosition().bearing;
                    float bearing = (float) Utils.bearingBetweenLocations(beginLatLng, endLatLng);
                    float angle = -azimuthInDegress + bearing;
                    float rotation = -azimuthInDegress * 360 / (2 * 3.14159f);
                    double lng = lngDelta * t + beginLatLng.longitude;
                /*
                if(bearing>0.0) {
                    marker.setPosition(new LatLng(lat, lng));
                    marker.setAnchor(0.5f, 0.5f);
                    marker.setFlat(true);
                    marker.setRotation(bearing);
                }else{
                    marker.setPosition(new LatLng(lat, lng));
                    marker.setAnchor(0.5f, 0.5f);
                    marker.setFlat(true);
                }
                 */
                    if (t < 1.0) {
                        tmpHandler.postDelayed(this, 16);
                    }
//                    else {
//                        float beginAngle = (float) (90 * Utils.getAngle(beginLatLng, endLatLng) / Math.PI);
//                        float endAngle = (float) (90 * Utils.getAngle(currentGpsPosition, endLatLng) / Math.PI);
//                        computeRotation(10, beginAngle, endAngle);
//                    }
                }
            };
        }

        tmpHandler.post(animateCarMoveNotUpdateMarkerRunnable);
    }

    private void unInitializeAllHandler() {
        if (startNavigationHandler != null) {
            if (startNavigationRunnable != null) {
                startNavigationHandler.removeCallbacks(startNavigationRunnable);
            }

            startNavigationHandler = null;
        }
        startNavigationRunnable = null;

        if (animateCarMoveHandler != null) {
            if (animateCarMoveRunnable != null) {
                animateCarMoveHandler.removeCallbacks(animateCarMoveRunnable);
            }
            animateCarMoveHandler = null;
        }
        animateCarMoveRunnable = null;

        if (animateCarMoveNotUpdateMarkerHandler != null) {
            if (animateCarMoveNotUpdateMarkerRunnable != null) {
                animateCarMoveNotUpdateMarkerHandler.removeCallbacks(animateCarMoveNotUpdateMarkerRunnable);
            }
            animateCarMoveNotUpdateMarkerHandler = null;
        }
        animateCarMoveNotUpdateMarkerRunnable = null;
    }

    public void writeLogFile() {
        if (isExternalStorageWritable()) {

            File appDirectory = new File(Environment.getExternalStorageDirectory() + "/RORO_AppLogs");
            File logDirectory = new File(appDirectory + "/log");
            File logFile = new File(logDirectory, "RORO_Log" + System.currentTimeMillis() + ".txt");

            // create app folder
            if (!appDirectory.exists()) {
                appDirectory.mkdir();
            }

            // create log folder
            if (!logDirectory.exists()) {
                logDirectory.mkdir();
            }

            // clear the previous logcat and then write the new one to the file
            try {
                Process process = Runtime.getRuntime().exec("logcat -c");
                process = Runtime.getRuntime().exec("logcat -f " + logFile);
            } catch (IOException e) {
                Log.e("WRITE LOG FILE", e.getMessage(), e);
                e.printStackTrace();
            }

        } else if (isExternalStorageReadable()) {
            // only readable
        } else {
            // not accessible
        }
    }


    /* Checks if external storage is available for read and write */
    public boolean isExternalStorageWritable() {
        String state = Environment.getExternalStorageState();
        if (Environment.MEDIA_MOUNTED.equals(state)) {
            return true;
        }
        return false;
    }

    /* Checks if external storage is available to at least read */
    public boolean isExternalStorageReadable() {
        String state = Environment.getExternalStorageState();
        if (Environment.MEDIA_MOUNTED.equals(state) ||
                Environment.MEDIA_MOUNTED_READ_ONLY.equals(state)) {
            return true;
        }
        return false;
    }

}
