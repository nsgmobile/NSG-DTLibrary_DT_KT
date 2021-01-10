package com.nsg.nsgdtlibrary.Classes.test;
import android.Manifest;
import android.Manifest.permission;
import android.animation.ValueAnimator;
import android.annotation.SuppressLint;
import android.app.Activity;
import android.app.AlertDialog;
import android.app.ProgressDialog;
import android.content.BroadcastReceiver;
import android.content.Context;
import android.content.DialogInterface;
import android.content.Intent;
import android.content.IntentFilter;
import android.content.pm.PackageManager;
import android.database.Cursor;
import android.graphics.Bitmap;
import android.graphics.BitmapFactory;
import android.graphics.Canvas;
import android.graphics.Color;
import android.graphics.Matrix;
import android.graphics.Point;
import android.graphics.drawable.Drawable;
import android.hardware.SensorManager;
import android.location.Criteria;
import android.location.Location;
import android.location.LocationManager;
import android.net.Uri;
import android.os.Build;
import android.os.Bundle;
import android.os.Environment;
import android.os.Handler;
import android.os.Looper;
import android.os.StrictMode;
import android.os.SystemClock;
import android.provider.Settings;
import android.speech.tts.TextToSpeech;
import android.util.Log;
import android.view.Gravity;
import android.view.LayoutInflater;
import android.view.MenuItem;
import android.view.View;
import android.view.ViewGroup;
import android.view.animation.Interpolator;
import android.view.animation.LinearInterpolator;
import android.widget.Button;
import android.widget.EditText;
import android.widget.ImageButton;
import android.widget.ImageView;
import android.widget.PopupMenu;
import android.widget.TextView;
import android.widget.Toast;

import com.google.android.gms.common.api.GoogleApiClient;

import com.google.android.gms.common.internal.Constants;
import com.google.android.gms.location.FusedLocationProviderClient;
import com.google.android.gms.location.LocationCallback;
import com.google.android.gms.location.LocationListener;
import com.google.android.gms.location.LocationRequest;
import com.google.android.gms.location.LocationResult;
import com.google.android.gms.maps.CameraUpdate;
import com.google.android.gms.maps.CameraUpdateFactory;
import com.google.android.gms.maps.GoogleMap;
import com.google.android.gms.maps.LocationSource;
import com.google.android.gms.maps.OnMapReadyCallback;
import com.google.android.gms.maps.Projection;
import com.google.android.gms.maps.SupportMapFragment;
import com.google.android.gms.maps.model.BitmapDescriptor;
import com.google.android.gms.maps.model.BitmapDescriptorFactory;
import com.google.android.gms.maps.model.CameraPosition;
import com.google.android.gms.maps.model.Circle;
import com.google.android.gms.maps.model.CircleOptions;
import com.google.android.gms.maps.model.JointType;
import com.google.android.gms.maps.model.LatLng;
import com.google.android.gms.maps.model.MapStyleOptions;
import com.google.android.gms.maps.model.Marker;
import com.google.android.gms.maps.model.MarkerOptions;
import com.google.android.gms.maps.model.Polyline;
import com.google.android.gms.maps.model.PolylineOptions;
import com.google.android.gms.maps.model.TileOverlay;
import com.google.android.gms.maps.model.TileOverlayOptions;
import com.google.android.gms.maps.model.TileProvider;
import com.google.android.gms.tasks.OnSuccessListener;
import com.google.maps.android.SphericalUtil;
import com.nsg.nsgdtlibrary.Classes.activities.AppConstants;
import com.nsg.nsgdtlibrary.Classes.activities.ExpandedMBTilesTileProvider;
import com.nsg.nsgdtlibrary.Classes.activities.GPSTracker;
import com.nsg.nsgdtlibrary.Classes.activities.GpsUtils;
import com.nsg.nsgdtlibrary.Classes.database.db.SqlHandler;
import com.nsg.nsgdtlibrary.Classes.database.dto.EdgeDataT;
import com.nsg.nsgdtlibrary.Classes.database.dto.GeometryT;
import com.nsg.nsgdtlibrary.Classes.database.dto.RouteT;
import com.nsg.nsgdtlibrary.Classes.util.DecimalUtils;
import com.nsg.nsgdtlibrary.Classes.util.ETACalclator;
import com.nsg.nsgdtlibrary.Classes.util.MapEvents;
import com.nsg.nsgdtlibrary.Classes.util.NavigationProperties;
import com.nsg.nsgdtlibrary.R;

import org.json.JSONArray;
import org.json.JSONException;
import org.json.JSONObject;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.OutputStream;
import java.io.OutputStreamWriter;
import java.net.HttpURLConnection;
import java.net.URL;
import java.text.DateFormat;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Date;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Locale;
import java.util.Map;
import java.util.Set;
import java.util.Timer;
import java.util.TimerTask;

import androidx.annotation.NonNull;
import androidx.annotation.Nullable;
import androidx.annotation.RequiresApi;
import androidx.core.app.ActivityCompat;
import androidx.core.content.ContextCompat;
import androidx.fragment.app.Fragment;
import de.siegmar.fastcsv.reader.CsvReader;

import com.google.android.gms.common.ConnectionResult;
import com.google.android.gms.common.GooglePlayServicesUtil;
import com.google.android.gms.common.api.GoogleApiClient;
import com.google.android.gms.common.api.PendingResult;
import com.google.android.gms.common.api.Status;
//import com.google.android.gms.location.LocationListener;
import com.google.android.gms.location.LocationRequest;
import com.google.android.gms.location.LocationServices;

//import static android.Manifest.permission.ACCESS_FINE_LOCATION;
//import static android.Manifest.permission.READ_EXTERNAL_STORAGE;
//import static android.content.Context.LOCATION_SERVICE;
import static android.Manifest.permission.ACCESS_FINE_LOCATION;
import static android.Manifest.permission.READ_EXTERNAL_STORAGE;
import static android.content.Context.LOCATION_SERVICE;
import static androidx.core.content.PermissionChecker.checkSelfPermission;
import static java.lang.Math.atan2;
import static java.lang.Math.cos;
import static java.lang.Math.sin;

public class NSGINavigationFragment extends Fragment implements View.OnClickListener {
    private boolean isAlertShown=false;
    private static final int PERMISSION_REQUEST_CODE = 200;
    boolean locationAccepted,islocationControlEnabled=false;
    // private static final int SENSOR_DELAY_NORMAL =50;
    boolean isTimerStarted=false;
    private ProgressDialog dialog;
    private TextToSpeech textToSpeech;
    LatLng SourcePosition, DestinationPosition,OldGPSPosition,PointBeforeRouteDeviation;
    double sourceLat, sourceLng, destLat, destLng;
    Marker mPositionMarker;
    // private Polyline mPolyline;
    private GoogleMap mMap;
    private SqlHandler sqlHandler;
    GoogleMap.CancelableCallback callback;
    private double TotalRouteDeviatedDistanceInMTS;
    private List points;
    private List<LatLng> convertedPoints;
    StringBuilder sb = new StringBuilder();
    private List LocationPerpedicularPoints=new ArrayList();
    private ArrayList<LatLng> currentLocationList=new ArrayList<LatLng>();
    private Marker sourceMarker,destinationMarker;
    private List<EdgeDataT> edgeDataList;
    private List<GeometryT> geometryRouteDeviatedEdgesData;
    List RouteDeviationConvertedPoints;
    private List<LatLng>RouteDeviationPointsForComparision;
    private List<RouteT> RouteDataList;
    private List PreviousGpsList;
    private Handler handler = new Handler();
    private int enteredMode;
    private Marker carMarker;
    private int routeDeviationDistance;
    List<LatLng> LatLngDataArray=new ArrayList<LatLng>();
    private String currentGpsPoint;
    private Polyline line;
    private List polyLines;
    private Circle mCircle;
    private List<LatLng>lastGPSPosition;
    private LatLng nearestPositionPoint;
    Bitmap mMarkerIcon;
    int mIndexCurrentPoint=0;
    private List<LatLng> edgeDataPointsList ;
    Map<String, List> mapOfLists = new HashMap<String, List>();
    private List AllPointsList ;
    HashMap<String,String> AllPointEdgeNo;
    HashMap<String,String> AllPointEdgeDistaces;
    private LatLng newCenterLatLng,PointData;
    private List distanceValuesList;
    private List<LatLng> nearestPointValuesList;
    private Marker gpsMarker;
    private TextView tv,tv1,tv2,tv3,tv4,tv5;
    private String routeIDName;
    HashMap<LatLng,String>edgeDataPointsListData;
    private ImageButton change_map_options,re_center;
    private String geometryDirectionText="",key="",distanceKey="",geometryDirectionDistance="";
    HashMap<String,String>nearestValuesMap;
    private List<LatLng> OldNearestGpsList;
    //  private int locationFakeGpsListener=0;
    //  String GeometryDirectionText="";
    private double vehicleSpeed;
    private double maxSpeed=30;
    private boolean isMarkerRotating=false;
    private String BASE_MAP_URL_FORMAT;
    private LatLng SourceNode,DestinationNode;
    LatLng currentGpsPosition,RouteDeviatedSourcePosition;
    float azimuthInDegress;
    Timer myTimer =new Timer();
    private String TotalDistance,stNode,endNode,routeDeviatedDT_URL="",AuthorisationKey;
    double TotalDistanceInMTS;
    private List<EdgeDataT> EdgeContainsDataList;
    private double resultNeedToTeavelTimeConverted;
    RouteT route;
    boolean isRouteDeviated=false;
    // private Button location_tracking_start,location_tracking_stop;
    StringBuilder time= new StringBuilder();
    LatLng nPosition= null;
    private String routeData;
    public boolean isMapLoaded=false;
    public boolean isNavigationStarted=false;
    NavigationProperties properties;
    LocationManager mLocationManager;
    private String directionTextRouteDeviation,st_vertex,end_vertex;
    private FusedLocationProviderClient mFusedLocationClient;
    private double wayLatitude = 0.0, wayLongitude = 0.0;
    private LocationRequest locationRequest;
    private LocationCallback locationCallback;
    private Button btnLocation;
    private TextView txtLocation;
    private Button btnContinueLocation;
    private TextView txtContinueLocation;
    private StringBuilder stringBuilder;
    LatLng currentGPSPosition;
    private boolean isContinue=true ;
    private boolean isGPS = false;
    List <LatLng> commonPoints;
    List <LatLng> new_unCommonPoints;
    public boolean isContinuoslyOutOfTrack=false;
    public boolean isnotRouteDeviated=true;
    int caluclateDistanceFlag=1;
    List<Double> consDistList=new ArrayList<>();
    private int buffersize;
    private EditText dynamic_buffer;
    private Button submit;
    List<Double> consRouteDeviatedDistList=new ArrayList<>();

    String s1,s2;

    public interface FragmentToActivity {
        // String communicate(String comm);
        String communicate(String comm, int alertType);
    }
    private FragmentToActivity Callback;
    public NSGINavigationFragment(){

    }
    @SuppressLint("ValidFragment")
    public NSGINavigationFragment(String BASE_MAP_URL_FORMAT) {
        NSGINavigationFragment.this.BASE_MAP_URL_FORMAT = BASE_MAP_URL_FORMAT;
    }
    @SuppressLint("ValidFragment")
    public NSGINavigationFragment(String BASE_MAP_URL_FORMAT,String stNode,String endNode, String routeData,int buffersize,String routeDeviatedDT_URL,String AuthorisationKey) {
        NSGINavigationFragment.this.BASE_MAP_URL_FORMAT = BASE_MAP_URL_FORMAT;
        NSGINavigationFragment.this.stNode=stNode;
        NSGINavigationFragment.this.endNode=endNode;
        NSGINavigationFragment.this.buffersize=buffersize;
        NSGINavigationFragment.this.routeData=routeData;
        NSGINavigationFragment.this.routeDeviatedDT_URL=routeDeviatedDT_URL;
        NSGINavigationFragment.this.AuthorisationKey=AuthorisationKey;

    }
    @Override
    public void onCreate(Bundle savedInstanceState) {
        super.onCreate(savedInstanceState);
        setHasOptionsMenu(true);
        mLocationManager = (LocationManager)getActivity().getSystemService(LOCATION_SERVICE);
        if (savedInstanceState == null) {
            textToSpeech = new TextToSpeech(getContext(), new TextToSpeech.OnInitListener() {
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

        //Initialise Fused Location Client
        mFusedLocationClient = LocationServices.getFusedLocationProviderClient(getActivity());
        //Initialise Location Listener
        locationRequest = LocationRequest.create();
        //Initialise Accuracy
        locationRequest.setPriority(LocationRequest.PRIORITY_HIGH_ACCURACY);
        //Initialise interval
        locationRequest.setInterval(10 * 1000); // 10 seconds
        // locationRequest.setFastestInterval(5 * 1000); // 5 seconds

        new GpsUtils(getContext()).turnGPSOn(new GpsUtils.onGpsListener() {
            @Override
            public void gpsStatus(boolean isGPSEnable) {
                // turn on GPS
                isGPS = isGPSEnable;
            }
        });
        //getLocation callback Method for get location
        locationCallback = new LocationCallback() {
            @Override
            public void onLocationResult(LocationResult locationResult) {
                // if(islocationControlEnabled==false) {
                if (locationResult == null) {
                    return;
                }
                for (Location location : locationResult.getLocations()) {
                    if (location != null) {

                        wayLatitude = location.getLatitude();
                        wayLongitude = location.getLongitude();
                        if (!isContinue) {
                            txtLocation.setText(String.format(Locale.US, "%s - %s", wayLatitude, wayLongitude));
                            //  Log.v("APP DATA", "APP DATA DATA ........ IF " );
                        } else {
                            stringBuilder.append(wayLatitude);
                            stringBuilder.append("-");
                            stringBuilder.append(wayLongitude);
                            stringBuilder.append("\n\n");
                            currentGPSPosition = new LatLng(wayLatitude, wayLongitude);
                        }
                    }
                }
            }
        };
        writeLogFile();
    }
    @Override
    public void onAttach(Context context) {
        super.onAttach(context);
        try {
            sqlHandler = new SqlHandler(getContext());// Sqlite handler
            Callback = (FragmentToActivity) context;
        } catch (ClassCastException e) {
            throw new ClassCastException(context.toString()
                    + " must implement FragmentToActivity");
        }
    }
    @RequiresApi(api = Build.VERSION_CODES.KITKAT)
    @Override
    public View onCreateView(LayoutInflater inflater, ViewGroup container,
                             Bundle savedInstanceState) {
        //Check self permissions for Location and storage
        checkPermission();
        //Request permissions for Location and storage
        requestPermission();
        //set marker icon
        mMarkerIcon = BitmapFactory.decodeResource(getResources(), R.drawable.gps_transperent_98);
        //Initialise RootView
        View rootView = inflater.inflate(R.layout.fragment_map, container, false);
        //Initialise Buttons
        re_center=(ImageButton)rootView.findViewById(R.id.re_center);
        re_center.setOnClickListener(NSGINavigationFragment.this);
        change_map_options = (ImageButton)rootView.findViewById(R.id.change_map_options);
        change_map_options.setOnClickListener(NSGINavigationFragment.this);

       // dynamic_buffer = (EditText)rootView.findViewById(R.id.dynamic_buffer);
        // dynamic_buffer.setOnClickListener(NSGINavigationFragment.this);


       // submit = (Button)rootView.findViewById(R.id.submit);
       // submit.setOnClickListener(NSGINavigationFragment.this);


        // Delete Contents fron ROUTE_T On initialisation of Route view
        String delQuery = "DELETE  FROM " + RouteT.TABLE_NAME;
        sqlHandler.executeQuery(delQuery);
        /* Insert NewDatata According to  SourceNode,DestinationNode,RouteData To local Database Coloumns*/
        if(stNode!=null && endNode!=null && routeData!=null){
            InsertAllRouteData(stNode,endNode,routeData);
            getRouteAccordingToRouteID(stNode,endNode);
            if(RouteDataList!=null && RouteDataList.size()>0) {
                route = RouteDataList.get(0);
                String routeDataFrmLocalDB = route.getRouteData();
                String sourceText=route.getStartNode();
                String[]  text =sourceText.split(" ");
                sourceLat= Double.parseDouble(text[1]);
                sourceLng= Double.parseDouble(text[0]);
                String destinationText=route.getEndNode();
                String[]  text1 =destinationText.split(" ");
                destLat= Double.parseDouble(text1[1]);
                destLng= Double.parseDouble(text1[0]);
                // SourceNode=new LatLng(sourceLat,sourceLng);
                //  DestinationNode=new LatLng(destLat,destLng);
            }
        }
        //Initialise Map fragment
        SupportMapFragment mapFragment = (SupportMapFragment) getChildFragmentManager().findFragmentById(R.id.frg);  //use SuppoprtMapFragment for using in fragment instead of activity  MapFragment1 = activity   SupportMapFragment = fragment
        mapFragment.getMapAsync(new OnMapReadyCallback() {
            @Override
            public void onMapReady(GoogleMap googlemap) {
                if (BASE_MAP_URL_FORMAT != null) {
                    //Initialise GoogleMap
                    NSGINavigationFragment.this.mMap = googlemap;
                    //mMap.setMapType(GoogleMap.MAP_TYPE_NONE);
                    //set GoogleMap Style
                    NSGINavigationFragment.this.mMap.setMapStyle(MapStyleOptions.loadRawResourceStyle(getContext(), R.raw.stle_map_json));
                    //set  Tileprovider to GoogleMap
                  //  TileProvider tileProvider = new ExpandedMBTilesTileProvider(new File(BASE_MAP_URL_FORMAT.toString()), 256, 256);
                  //  TileOverlay tileOverlay = mMap.addTileOverlay(new TileOverlayOptions().tileProvider(tileProvider));
                  //  tileOverlay.setTransparency(0.5f - tileOverlay.getTransparency());
                  //  tileOverlay.setVisible(true);
                    if (routeData != null) {
                        /*Get Route From Database and plot on map*/
                        GetRouteFromDBPlotOnMap(routeData);
                        StringBuilder routeAlert = new StringBuilder();
                        routeAlert.append(MapEvents.ALERTVALUE_1).append("SourcePosition : " + SourceNode).append("Destination Node " + DestinationNode);
                        //send alert AlertTupe-1 -- started
                        sendData(routeAlert.toString(), MapEvents.ALERTTYPE_1);
                    }
                    //get all edges data from local DB
                    getAllEdgesData();
                    // get Valid Routedata acc to Map
                    getValidRouteData();
                    //Adding markers on map
                    addMarkers();
                    if (ActivityCompat.checkSelfPermission(getContext(), ACCESS_FINE_LOCATION) != PackageManager.PERMISSION_GRANTED && ActivityCompat.checkSelfPermission(getContext(), permission.ACCESS_COARSE_LOCATION) != PackageManager.PERMISSION_GRANTED) {
                        // TODO: Consider calling
                        //    ActivityCompat#requestPermissions
                        return;
                    }
                    //Sending Alert Map is READY
                    isMapLoaded = true;
                    if(isMapLoaded==true ){
                        String MapAlert="Map is Ready";
                        sendData(MapEvents.ALERTVALUE_6,MapEvents.ALERTTYPE_6);
                    }

                }
            }
        });
        return rootView;
    }
    @Override
    public void onClick(View v) {
        if(v==change_map_options){
                /*
                Changing Map options on button click To MAP_TYPE_NORMAL,MAP_TYPE_SATELLITE,MAP_TYPE_TERRAIN,MAP_TYPE_HYBRID
                 */

            PopupMenu popup = new PopupMenu(getContext(), change_map_options);
            //Inflating the Popup using xml file
            popup.getMenuInflater()
                    .inflate(R.menu.popup_menu, popup.getMenu());
            //registering popup with OnMenuItemClickListener
            popup.setOnMenuItemClickListener(new PopupMenu.OnMenuItemClickListener() {
                public boolean onMenuItemClick(MenuItem item) {
                    int itemId = item.getItemId();
                    if (itemId == R.id.slot1) {
                        if(mMap!=null) {
                            mMap.setMapType(GoogleMap.MAP_TYPE_NORMAL);
                            //  Toast.makeText(getContext(), "NORMAL MAP ENABLED", Toast.LENGTH_SHORT).show();
                        }
                        return true;
                    } else if (itemId == R.id.slot2) {
                        if(mMap!=null) {
                            mMap.setMapType(GoogleMap.MAP_TYPE_SATELLITE);
                            //  Toast.makeText(getContext(), "SATELLITE MAP ENABLED", Toast.LENGTH_SHORT).show();
                        }
                        return true;
                    } else if (itemId == R.id.slot3) {
                        if(mMap!=null) {
                            mMap.setMapType(GoogleMap.MAP_TYPE_TERRAIN);
                            // Toast.makeText(getContext(), "TERRAIN MAP ENABLED", Toast.LENGTH_SHORT).show();
                        }
                        return true;
                    }else if (itemId == R.id.slot4) {
                        if(mMap!=null) {
                            mMap.setMapType(GoogleMap.MAP_TYPE_HYBRID);
                            //  Toast.makeText(getContext(), "HYBRID MAP ENABLED", Toast.LENGTH_SHORT).show();
                        }
                        return true;
                    }
                    return true;
                }
            });
            popup.show();
        }else if(v==re_center){
                /*
                Recenter Button if map enabled and location enabled get location from map and update map position and
                recenter to  the position captured
                 */
            mMap.setMyLocationEnabled(true);
            if(mPositionMarker!=null){
                LatLng myLocation=null;
                myLocation= mPositionMarker.getPosition();
                int height=0;
                if(getView()!=null ) {
                    height = getView().getMeasuredHeight();
                }
                mMap.moveCamera(CameraUpdateFactory.newLatLng(myLocation));
                mMap.animateCamera(CameraUpdateFactory.zoomTo(18));
            }

        }else if(v==submit){
            //String buffer_distance = dynamic_buffer.getText().toString();
            if(!dynamic_buffer.getText().toString().isEmpty()) {
                int val = Integer.parseInt(dynamic_buffer.getText().toString());
                routeDeviationDistance = val;
                Log.e("Route Deviation Buffer", " Deviation Buffer Test---- " + routeDeviationDistance);
            }else{
                routeDeviationDistance = 10;
            }
        }
    }
    public int startNavigation() {
            /*
                Starts Navigation HERE
                Get current location from the location service if map enabled true then it will starts navigation
                from external service and strts navigation if route deviation not observed move in the loaded path
                if route deviation observed movement from route deviated path only
             */
        islocationControlEnabled=false;
        Log.v("APP DATA ", "islocationControlEnabled START BUTTON GPS POSITION ----" + OldGPSPosition);
        if (SourceNode != null && DestinationNode != null ) {
            nearestPointValuesList = new ArrayList<LatLng>();
            nearestPointValuesList.add(new LatLng(sourceLat, sourceLng));
            OldNearestGpsList = new ArrayList<>();
            OldNearestGpsList.add(new LatLng(sourceLat, sourceLng));
            try {
                if (mMap != null && isMapLoaded == true && isNavigationStarted == false) {
                    if (isTimerStarted = true) {
                        myTimer.schedule(new TimerTask() {
                            @Override
                            public void run() {
                                if (currentGpsPosition != null && DestinationNode != null) {
                                    if(islocationControlEnabled==false) {
                                        if (isRouteDeviated == false) {
                                            if(isContinuoslyOutOfTrack==false) {
                                                NavigationDirection(currentGpsPosition, DestinationNode);
                                            }
                                        }else{
                                            if(directionTextRouteDeviation!=null && st_vertex!=null && end_vertex!=null) {
                                                TextImplementationRouteDeviationDirectionText(directionTextRouteDeviation, st_vertex, end_vertex);
                                            }
                                        }

                                    }else{

                                    }
                                }
                            }

                        }, 0, 15000);
                    }
                    mMap.setMyLocationEnabled(true);
                    mMap.setBuildingsEnabled(true);
                    mMap.getUiSettings().setZoomControlsEnabled(true);
                    mMap.getUiSettings().setCompassEnabled(true);
                 //   mMap.getUiSettings().setMyLocationButtonEnabled(false);
                    mMap.getUiSettings().setMapToolbarEnabled(true);
                    mMap.getUiSettings().setZoomGesturesEnabled(true);
                    mMap.getUiSettings().setScrollGesturesEnabled(true);
                    mMap.getUiSettings().setTiltGesturesEnabled(true);
                    mMap.getUiSettings().setRotateGesturesEnabled(true);
                   // mMap.getUiSettings().setMyLocationButtonEnabled(true);
                    isNavigationStarted = true;
                    if (Build.VERSION.SDK_INT >= Build.VERSION_CODES.JELLY_BEAN) {

                        isTimerStarted = true;
                        Handler handler = new Handler();
                        int delay = 1000 *1; // 1 second
                        handler.postDelayed(new Runnable() {
                            public void run() {
                                double returnedDistance_ref=0.0;

                                    if (currentGpsPosition != null) {
                                        OldGPSPosition = currentGpsPosition;
                                        Log.v("APP DATA ", "START NAV OLD GPS POSITION ----" + OldGPSPosition);
                                        returnedDistance_ref = verifyDeviationCalculateDistance(OldGPSPosition, currentGpsPosition);
                                        Log.e("APP DATA ", " Distance1 ----" + returnedDistance_ref);
                                    }
                                    consDistList.add(returnedDistance_ref);
                                    isContinue = true;
                                    stringBuilder = new StringBuilder();
                                    currentGpsPosition = getLocation();
                                    Log.v("APP DATA ", "START NAVI CURRENT GPS POSITION ----" + currentGpsPosition);
                                    // Navigation code starts from here
                                    LatLng OldNearestPosition = null;
                                    if (isRouteDeviated == false) {
                                        if (OldGPSPosition != null) {
                                                double distance = distFrom(OldGPSPosition.latitude, OldGPSPosition.longitude, currentGpsPosition.latitude, currentGpsPosition.longitude);
                                                Log.e("distance", "distance" + distance);
                                                if (distance > 40) {

                                                } else {
                                                    OldNearestPosition = nPosition;
                                                    Log.e("CurrentGpsPoint", " OLD Nearest GpsPoint " + OldNearestPosition);
                                                    nPosition = GetNearestPointOnRoadFromGPS(OldGPSPosition, currentGpsPosition);
                                                    Log.e("CurrentGpsPoint", " Nearest GpsPoint" + nPosition);
                                                    double distance_movement = distFrom(nPosition.latitude, nPosition.longitude, currentGpsPosition.latitude, currentGpsPosition.longitude);
                                                    Log.e("Distance_movement", " Distance_movement" + distance_movement);
                                                    if (distance_movement <40) {
                                                        if (mPositionMarker == null) {
                                                            mPositionMarker = mMap.addMarker(new MarkerOptions()
                                                                    .position(SourceNode)
                                                                    .title("Nearest GpsPoint")
                                                                    .anchor(0.5f, 0.5f)
                                                                    .flat(true)
                                                                    .icon(bitmapDescriptorFromVector(getContext(), R.drawable.gps_transperent_98)));
                                                        } else {
                                                            Log.e("CurrentGpsPoint", " currentGpsPosition ------ " + currentGpsPosition);
                                                            if (OldNearestPosition != null) {
                                                                if (islocationControlEnabled == false) {
                                                                    Log.e("CurrentGpsPoint", " curren FRM START NAVI ------ " + currentGpsPosition);
                                                                    Log.e("CurrentGpsPoint", " Old  FRM START NAVI ------ " + OldNearestPosition);
                                                                    Log.e("CurrentGpsPoint", " islocationControlEnabled FLAG------ " + islocationControlEnabled);
                                                                    animateCarMove(mPositionMarker, OldNearestPosition, nPosition, 1000);
                                                                    float bearing = (float) bearingBetweenLocations(OldNearestPosition, nPosition);
                                                                    Log.e("BEARING", "BEARING @@@@@@@ " + bearing);
                                                                    int height = 0;
                                                                    if (getView() != null) {
                                                                        height = getView().getMeasuredHeight();
                                                                    }
                                                                    Projection p = mMap.getProjection();
                                                                    Point bottomRightPoint = p.toScreenLocation(p.getVisibleRegion().nearRight);
                                                                    Point center = new Point(bottomRightPoint.x / 2, bottomRightPoint.y / 2);
                                                                    Point offset = new Point(center.x, (center.y + (height / 4)));
                                                                    LatLng centerLoc = p.fromScreenLocation(center);
                                                                    LatLng offsetNewLoc = p.fromScreenLocation(offset);
                                                                    double offsetDistance = SphericalUtil.computeDistanceBetween(centerLoc, offsetNewLoc);
                                                                    LatLng shadowTgt = SphericalUtil.computeOffset(nPosition, offsetDistance, bearing);
                                                                    caclulateETA(TotalDistanceInMTS, SourceNode, currentGpsPosition, DestinationNode);
                                                                    double returnedDistance1 = 0.0;
                                                                    double returnedDistance2 = 0.0;
                                                                    double returnedDistance3 = 0.0;
                                                                    if (consDistList != null) {
                                                                        returnedDistance1 = consDistList.get(consDistList.size() - 1);
                                                                        Log.e("APP DATA ", " Distance 1 ----" + returnedDistance1);
                                                                        returnedDistance2 = consDistList.get(consDistList.size() - 2);
                                                                        Log.e("APP DATA ", " Distance 2 ----" + returnedDistance2);
                                                                        returnedDistance3 = consDistList.get(consDistList.size() - 3);
                                                                        Log.e("APP DATA ", " Distance 3 ----" + returnedDistance3);
                                                                    }
                                                                    if (returnedDistance1 > routeDeviationDistance) {
                                                                        if (returnedDistance2 > routeDeviationDistance) {
                                                                            if (returnedDistance3 > routeDeviationDistance) {
                                                                                verifyRouteDeviationTask(OldGPSPosition, currentGpsPosition, DestinationNode, routeDeviationDistance, null);
                                                                            }
                                                                        }
                                                                    } else {

                                                                    }
                                                                    AlertDestination(currentGpsPosition);
                                                                    if (bearing > 0.0) {
                                                                        CameraPosition currentPlace = new CameraPosition.Builder()
                                                                                .target(shadowTgt)
                                                                                .bearing(bearing).tilt(65.5f).zoom(18)
                                                                                .build();
                                                                        mMap.animateCamera(CameraUpdateFactory.newCameraPosition(currentPlace), 1000, null);
                                                                    } else {

                                                                    }
                                                                } else if (islocationControlEnabled == true) {
                                                                    animateCarMoveNotUpdateMarker(mPositionMarker, OldNearestPosition, nPosition, 1000);
                                                                }


                                                            }
                                                        }
                                                    }else {
                                                        isContinuoslyOutOfTrack=true;
                                                        if (mPositionMarker == null) {
                                                            mPositionMarker = mMap.addMarker(new MarkerOptions()
                                                                    .position(currentGPSPosition)
                                                                    .title("Nearest GpsPoint")
                                                                    .anchor(0.5f, 0.5f)
                                                                    .flat(true)
                                                                    .icon(bitmapDescriptorFromVector(getContext(), R.drawable.gps_transperent_98)));
                                                        } else {
                                                            animateCarMove(mPositionMarker, OldGPSPosition, currentGPSPosition, 1000);
                                                            CameraPosition currentPlace = new CameraPosition.Builder()
                                                                    .target(currentGPSPosition)
                                                                    .tilt(65.5f).zoom(18)
                                                                    .build();
                                                            mMap.animateCamera(CameraUpdateFactory.newCameraPosition(currentPlace), 1000, null);
                                                            double returnedDistance1 = 0.0;
                                                            double returnedDistance2 = 0.0;
                                                            double returnedDistance3 = 0.0;
                                                            animateCarMove(mPositionMarker, OldGPSPosition, currentGPSPosition, 1000);
                                                            if (consDistList != null) {

                                                                returnedDistance1 = consDistList.get(consDistList.size() - 1);
                                                                Log.e("APP DATA ", " Distance 1 ----" + returnedDistance1);
                                                                returnedDistance2 = consDistList.get(consDistList.size() - 2);
                                                                Log.e("APP DATA ", " Distance 2 ----" + returnedDistance2);
                                                                returnedDistance3 = consDistList.get(consDistList.size() - 3);
                                                                Log.e("APP DATA ", " Distance 3 ----" + returnedDistance3);
                                                            }
                                                            if (returnedDistance1 > routeDeviationDistance) {
                                                                if (returnedDistance2 > routeDeviationDistance) {
                                                                    if (returnedDistance3 > routeDeviationDistance) {
                                                                        verifyRouteDeviationTask(OldGPSPosition, currentGpsPosition, DestinationNode, routeDeviationDistance, null);

                                                                    }
                                                                }
                                                            } else {

                                                            }
                                                            if(isContinuoslyOutOfTrack==true){
                                                                currentLocationList.add(currentGpsPosition);
                                                                PolylineOptions polylineOptions = new PolylineOptions();
                                                                // polylineOptions.add(OldGPSPosition);
                                                                polylineOptions.addAll(currentLocationList);
                                                                Polyline polyline = mMap.addPolyline(polylineOptions);
                                                                polylineOptions.color(Color.RED).width(30);
                                                                mMap.addPolyline(polylineOptions);
                                                                polyline.setJointType(JointType.ROUND);
                                                            }


                                                        }
                                                    }
                                                }

                                            }

                                   } else if(isRouteDeviated==true) {
                                       MoveWithGpsPointInRouteDeviatedPoints(currentGpsPosition);
                                   }
                                    //Navigation code ends here
                                handler.postDelayed(this, delay);
                            }

                        }, delay);


                        // }

                    }
                }

                return 1;
            } catch (Exception e) {
                return 0;
            }
        }
        //  }
        return 0;
    }
    public int stopNavigation(){
            /*
              StopNavigation if user enables stop navigation
              show ALERT TYPE-5  for stoppping map
             */
        try{
            islocationControlEnabled = true;
            if(SourceNode!=null && DestinationNode!=null) {
                if (mMap != null && isNavigationStarted == true && islocationControlEnabled==true ) {
                    isNavigationStarted = false;
                    islocationControlEnabled=false;
                    Log.e("STOP NAVIGATION", "STOP NAVIGATION INNER VALUE --"+ islocationControlEnabled);


                    if (mFusedLocationClient != null) {
                        // mFusedLocationClient = null;
                        mFusedLocationClient.removeLocationUpdates(locationCallback);
                        Log.e("STOP NAVIGATION", "STOP NAVIGATION");
                    }
                    if (currentGpsPosition != null) {
                        // String NavigationAlert = " Navigation Stopped " ;
                        String NavigationAlert = " Navigation Stopped " + currentGpsPosition;
                        sendData(MapEvents.ALERTVALUE_5, MapEvents.ALERTTYPE_5);
                        LayoutInflater inflater1 = getActivity().getLayoutInflater();
                        @SuppressLint("WrongViewCast") final View layout = inflater1.inflate(R.layout.custom_toast, (ViewGroup) getActivity().findViewById(R.id.textView_toast));
                        final TextView text = (TextView) layout.findViewById(R.id.textView_toast);
                        final ImageView image = (ImageView) layout.findViewById(R.id.image_toast);
                        Toast toast = new Toast(getActivity().getApplicationContext());
                        String stopText = "Navigation Stopped";
                        text.setText("" + stopText);
                        if (stopText.startsWith("Navigation Stopped")) {
                            image.setImageResource(R.drawable.stop_image);
                        }
                        toast.setDuration(Toast.LENGTH_LONG);
                        toast.setGravity(Gravity.TOP | Gravity.CENTER_HORIZONTAL, 0, 0);
                        toast.setGravity(Gravity.TOP, 0, 200);
                        toast.setView(layout);
                        toast.show();
                    }
                    // getActivity().onBackPressed();
                    islocationControlEnabled=false;
                    Log.e("STOP NAVIGATION", " islocationControlEnabled STOP NAVIGATION FLAG END VALUE "+ islocationControlEnabled);
                }
            }

            return 1;
        } catch(Exception e){
            return 0;
        }

    }
    @RequiresApi(api = Build.VERSION_CODES.JELLY_BEAN)
    public void verifyRouteDeviation(final LatLng PrevousGpsPosition, final LatLng currentGpsPosition, final LatLng DestinationPosition, int markDistance, final List<LatLng>EdgeWithoutDuplicates) {
               /*
              After getting current gps verifing in the  radius of
              in the routebetween the Previous and current gps position
              if Route deviation exists it shows the message Route Deviated it will get route from the service and plot route on map
               otherwise continue with the existed route
              */
        Log.e("Route Deviation", "CURRENT GPS ----" + currentGpsPosition);
        Log.e("Route Deviation", " OLD GPS POSITION  ----" + PrevousGpsPosition);
        if (PrevousGpsPosition != null){
             /*
             GetNearestPointOnRoadFromGPS(PrevousGpsPosition,currentGpsPosition)-- in this method PrevousGpsPosition is not using any where,
              we are sending it for
             handling parameter exception only ---
              */
            LatLng nearest_LatLng_deviation= GetNearestPointOnRoadFromGPS(PrevousGpsPosition,currentGpsPosition);
            double returnedDistance = showDistance(currentGpsPosition, nearest_LatLng_deviation);
            Log.e("Route Deviation","ROUTE DEVIATION DISTANCE RETURNED ---- "+returnedDistance);
            if(returnedDistance >routeDeviationDistance) {
                String cgpsLat = String.valueOf(currentGpsPosition.latitude);
                String cgpsLongi = String.valueOf(currentGpsPosition.longitude);
                final String routeDiationPosition = cgpsLongi.concat(" ").concat(cgpsLat);
                Log.e("Route Deviation", "routeDiationPosition   ######" + routeDiationPosition);

                String destLatPos = String.valueOf(DestinationPosition.latitude);
                String destLongiPos = String.valueOf(DestinationPosition.longitude);
                final String destPoint = destLongiPos.concat(" ").concat(destLatPos);
                RouteDeviatedSourcePosition = new LatLng(Double.parseDouble(cgpsLat), Double.parseDouble(cgpsLongi));
                Log.e("Route Deviation", "routeDiation SOURCE Position  ###### " + RouteDeviatedSourcePosition);
                Log.e("returnedDistance", "RouteDiationPosition  ###### " + routeDiationPosition);
                //   Log.e("returnedDistance", "Destination Position --------- " + destPoint);
                //  DestinationPosition = new LatLng(destLat, destLng);
                if (getActivity() != null){
                    dialog = new ProgressDialog(getActivity(), R.style.ProgressDialog);
                    dialog.setMessage("Fetching new Route");
                    dialog.setMax(100);
                    dialog.show();
                    getActivity().runOnUiThread(new Runnable() {
                        @Override
                        public void run() {
                            String MESSAGE = "";
                            GetRouteDetails(routeDiationPosition, destPoint);
                            if (RouteDeviationConvertedPoints != null && RouteDeviationConvertedPoints.size() > 0) {
                                List<LatLng> EdgeWithoutDuplicates = removeDuplicates(edgeDataPointsList);
                                List<LatLng> EdgeWithoutDuplicatesInRouteDeviationPoints = removeDuplicatesRouteDeviated(RouteDeviationPointsForComparision);
                                if (EdgeWithoutDuplicates != null && EdgeWithoutDuplicatesInRouteDeviationPoints != null) {
                                    checkPointsOfExistingRoutewithNewRoute(EdgeWithoutDuplicates, RouteDeviationPointsForComparision);

                                    Log.e("List Verification", "List Verification commonPoints --  DATA " + commonPoints.size());
                                    Log.e("List Verification", "List Verification  new_unCommonPoints -- DATA " + new_unCommonPoints.size());
                                    if (commonPoints.size() == 0) {
                                        if (mPositionMarker != null && mPositionMarker.isVisible() == true) {
                                            PolylineOptions polylineOptions = new PolylineOptions();
                                            // polylineOptions.add(OldGPSPosition);
                                            polylineOptions.addAll(RouteDeviationConvertedPoints);
                                            Polyline polyline = mMap.addPolyline(polylineOptions);
                                            polylineOptions.color(Color.RED).width(30);
                                            mMap.addPolyline(polylineOptions);
                                            polyline.setJointType(JointType.ROUND);
                                        }
                                        Log.e("List Verification", "List Verification  new_unCommonPoints -- DATA " + "NEW ROUTE");
                                        Log.e("Route Deviation", " IS ROUTE VERIFY  ###### " + " Route NOT EQUAL");
                                        isRouteDeviated = true;
                                    } else if (commonPoints.size() > 0) {
                                        if (new_unCommonPoints.size() > 5) {

                                            Log.e("Route Deviation", " IS ROUTE VERIFY  ###### " + " Route COINSIDENCE");
                                            if (mPositionMarker != null && mPositionMarker.isVisible() == true) {
                                                PolylineOptions polylineOptions = new PolylineOptions();
                                                // polylineOptions.add(OldGPSPosition);
                                                polylineOptions.addAll(new_unCommonPoints);
                                                Polyline polyline = mMap.addPolyline(polylineOptions);
                                                polylineOptions.color(Color.RED).width(30);
                                                mMap.addPolyline(polylineOptions);
                                                polyline.setJointType(JointType.ROUND);
                                            }
                                            LatLng markerPosition = mPositionMarker.getPosition();
                                            Log.e("Route Deviation", "RouteDeviation_RouteSt_point Distance Buffer --Marker _Position" + markerPosition);
                                            LatLng compare_pt = new_unCommonPoints.get(0);
                                            Log.e("Route Deviation", " IS ROUTE VERIFY   ###### Compare _point" + compare_pt);
                                            double compare_distance_pt = distFrom(markerPosition.latitude, markerPosition.longitude, compare_pt.latitude, compare_pt.longitude);
                                            consRouteDeviatedDistList.add(compare_distance_pt);
                                            Log.e("Route Deviation", " IS ROUTE VERIFY   ###### consRouteDeviatedDistList " + consRouteDeviatedDistList.size());

                                            if (consRouteDeviatedDistList != null && consRouteDeviatedDistList.size() > 3) {
                                                double routeDeviated_distance_1 = consRouteDeviatedDistList.get(consRouteDeviatedDistList.size() - 1);
                                                double routeDeviated_distance_2 = consRouteDeviatedDistList.get(consRouteDeviatedDistList.size() - 2);
                                                double routeDeviated_distance_3 = consRouteDeviatedDistList.get(consRouteDeviatedDistList.size() - 3);


                                                if (routeDeviated_distance_1 > 20) {
                                                    Log.e("Route Deviation", " Inside Route Deviation Distance " + routeDeviated_distance_1);
                                                    if (routeDeviated_distance_2 > 20) {
                                                        Log.e("Route Deviation", " Inside Route Deviation Distance " + routeDeviated_distance_2);
                                                        if (routeDeviated_distance_3 > 20) {
                                                            Log.e("Route Deviation", " Inside Route Deviation Distance " + routeDeviated_distance_3);
                                                            isRouteDeviated = true;
                                                            LayoutInflater inflater1 = getActivity().getLayoutInflater();
                                                            @SuppressLint("WrongViewCast") View layout = inflater1.inflate(R.layout.custom_toast, (ViewGroup) getActivity().findViewById(R.id.textView_toast));
                                                            TextView text = (TextView) layout.findViewById(R.id.textView_toast);
                                                            text.setText("Route Deviated");
                                                            Toast toast = new Toast(getActivity().getApplicationContext());
                                                            toast.setDuration(Toast.LENGTH_LONG);
                                                            toast.setGravity(Gravity.TOP | Gravity.CENTER_HORIZONTAL, 0, 0);
                                                            toast.setGravity(Gravity.TOP, 0, 150);
                                                            toast.setView(layout);
                                                            toast.show();
                                                            StringBuilder routeDeviatedAlert = new StringBuilder();
                                                            routeDeviatedAlert.append("ROUTE DEVIATED" + " RouteDeviatedSourcePosition : " + RouteDeviatedSourcePosition);
                                                            sendData(MapEvents.ALERTVALUE_3, MapEvents.ALERTTYPE_3);
                                                            Log.e("Route Deviation", " Route Deviation Alert POSTED" + MapEvents.ALERTVALUE_3);
                                                        }
                                                    }
                                                }
                                            }
                                            if(currentGpsPosition.toString().startsWith("lat/lng: (")){

                                            }else {
                                                MoveWithGpsPointInRouteDeviatedPoints(currentGpsPosition);
                                            }

                                        } else {

                                        }
                                    } else if (new_unCommonPoints.size() == 0) {
                                        Log.e("List Verification", "List Verification  new_unCommonPoints -- DATA " + " OLD ROUTE");

                                    }
                                }


                            }


                        }
                    });
                }

            }

        }else{

        }
    }


    public void onDestroy() {
        super.onDestroy();
        if(textToSpeech!=null) {
            textToSpeech.shutdown();
        }
        if(mFusedLocationClient!=null) {
            mFusedLocationClient = null;
        }
    }


    @Override
    public void onDetach() {
        super.onDetach();
        // Callback = null;
    }
    private  List<RouteT> getRouteAccordingToRouteID(String stNode,String endNode) {
        String query = "SELECT * FROM " + RouteT.TABLE_NAME +" WHERE startNode = "+"'"+stNode+"'"+" AND "+ "endNode= "+ "'"+endNode+"'";
        //Log.e("QUERY","QUERY"+ query);
        Cursor c1 = sqlHandler.selectQuery(query);
        RouteDataList = (List<RouteT>) SqlHandler.getDataRows(RouteT.MAPPING, RouteT.class, c1);
        sqlHandler.closeDataBaseConnection();
        return RouteDataList;
    }



    @RequiresApi(api = Build.VERSION_CODES.JELLY_BEAN)
    public LatLng GetNearestPointOnRoadFromGPS(final LatLng OldGpsPosition,final LatLng currentGpsPosition){
            /*
               Internal calculation to get Nearest POINT   TO CGPS position on Map using EDGESDATA
               calculating first shoretest and second shortest position from the edges data
               and calulate nearest position from the data
             */
        List distancesList=new ArrayList();
        HashMap<String,String>  hash_map=new HashMap<>();
        String FirstCordinate=null,SecondCordinate=null;
        LatLng newGPS=null;
        List<LatLng> EdgeWithoutDuplicates = removeDuplicates(edgeDataPointsList);
        if (EdgeWithoutDuplicates != null && EdgeWithoutDuplicates.size() > 0) {
            for (int epList = 0; epList < EdgeWithoutDuplicates.size(); epList++) {
                LatLng poinOnROAD = EdgeWithoutDuplicates.get(epList);
                double distance = distFrom(poinOnROAD.latitude,poinOnROAD.longitude,currentGpsPosition.longitude,currentGpsPosition.latitude);
                distancesList.add(distance);
                hash_map.put(String.valueOf(distance),poinOnROAD.toString());
                Collections.sort(distancesList);
            }
            String FirstShortestDistance = String.valueOf(distancesList.get(0));
            String SecondShortestDistance = String.valueOf(distancesList.get(1));

            boolean answerFirst= hash_map.containsKey(FirstShortestDistance);
            if (answerFirst) {

                FirstCordinate = (String)hash_map.get(FirstShortestDistance);
                key= String.valueOf(getKeysFromValue(AllPointEdgeNo,FirstCordinate));
                distanceKey= String.valueOf(getKeysFromValue(AllPointEdgeDistaces,FirstCordinate));
            }
            boolean answerSecond= hash_map.containsKey(SecondShortestDistance);
            if (answerSecond) {
                SecondCordinate = (String)hash_map.get(SecondShortestDistance);

            }
            if(FirstCordinate != null && SecondCordinate != null)
            {
                String First= FirstCordinate.replace("lat/lng: (","");
                First = First.replace(")","");

                String[] FirstLatLngsData=First.split(",");

                double FirstLatitude= Double.valueOf(FirstLatLngsData[0]);
                double FirstLongitude= Double.valueOf(FirstLatLngsData[1]);



                String Second= SecondCordinate.replace("lat/lng: (","");
                Second= Second.replace(")","");

                String[] SecondLatLngsData=Second.split(",");

                double SecondLatitude= Double.valueOf(SecondLatLngsData[0]);
                double SecondLongitude= Double.valueOf(SecondLatLngsData[1]);

                LatLng source=new LatLng(FirstLongitude,FirstLatitude);
                LatLng destination=new LatLng(SecondLongitude,SecondLatitude);

                newGPS= findNearestPoint(currentGpsPosition,source,destination);
            }
        }
        return newGPS;
    }
    public String NavigationDirection(final LatLng currentGpsPosition, LatLng DestinationPosition) {
             /*
               Internal calculation to get shortest Distance point  from CGPS position in Route Data
             */
        final String shortestDistancePoint = "";

        ArrayList<Double> EdgeDistancesList=new ArrayList<Double>();
        HashMap EdgeDistancesMap=new HashMap<String,String>();
        String stPoint = "", endPoint = "", geometryTextimpValue = "", distanceInEdge = "";
        String position="";
        for(int k=0;k<EdgeContainsDataList.size();k++){
            EdgeDataT edgeK=EdgeContainsDataList.get(k);
            StringBuilder sb=new StringBuilder();
            sb.append("STPOINT :"+edgeK.getStartPoint()+"EndPt:"+edgeK.getEndPoint()+"Points:"+edgeK.getPositionMarkingPoint()+"Geometry TEXT:"+ edgeK.getGeometryText());

            String pointDataText=edgeK.getPositionMarkingPoint();
            String stPoint_data=pointDataText.replace("lat/lng: (","");
            String stPoint_data1=stPoint_data.replace(")","");
            String[] st_point=stPoint_data1.split(",");
            double st_point_lat= Double.parseDouble(st_point[1]);
            double st_point_lnag= Double.parseDouble(st_point[0]);
            LatLng st_Point_vertex_main=new LatLng(st_point_lnag,st_point_lat);
            double distanceOfCurrentPosition=showDistance(st_Point_vertex_main,currentGpsPosition);
            EdgeDistancesList.add(distanceOfCurrentPosition);
            EdgeDistancesMap.put(String.valueOf(distanceOfCurrentPosition).trim(),String.valueOf(pointDataText));
            Collections.sort(EdgeDistancesList);
        }

        GetSortetPoint(EdgeDistancesMap,EdgeDistancesList, currentGpsPosition );
        return shortestDistancePoint;

    }
    public String  GetSortetPoint(HashMap EdgeDistancesMap, ArrayList<Double>  EdgeDistancesList, LatLng currentGpsPosition ){
              /*
            Internal calculation to get shortest point  from CGPS position , using Edges from the Route Data
             */
        String vfinalValue = "";
        String FirstShortestDistance = String.valueOf(EdgeDistancesList.get(0));
        boolean verify=EdgeDistancesMap.containsKey(FirstShortestDistance.trim());
        if(verify){

            Object Value =String.valueOf( EdgeDistancesMap.get(FirstShortestDistance));
            vfinalValue= String.valueOf(EdgeDistancesMap.get(FirstShortestDistance));

        } else{
            System.out.println("Key not matched with ID");
        }

        EdgesEndContaingData(currentGpsPosition,vfinalValue);

        return vfinalValue;
    }
    public void EdgesEndContaingData(LatLng currentGpsPosition, String shortestDistancePoint){
         /*
            Internal calculation to get Edges of CGPS point -- it gets shortest point with the edges
            using shotest distance from CGPS position
         */
        String stPoint = "", endPoint = "", geometryTextimpValue = null, distanceInEdge = "";
        String position="";
        int indexPosition=0;
        EdgeDataT edgeCurrentPoint= null;
        StringBuilder sb=new StringBuilder();
        for(int i=0;i<EdgeContainsDataList.size();i++){
            edgeCurrentPoint=EdgeContainsDataList.get(i);
            position=edgeCurrentPoint.getPositionMarkingPoint();
            if(position.equals(shortestDistancePoint)){
                distanceInEdge=EdgeContainsDataList.get(i).getGeometryText();
                stPoint=  EdgeContainsDataList.get(i).getStartPoint();
                endPoint= EdgeContainsDataList.get(i).getEndPoint();
                geometryTextimpValue=EdgeContainsDataList.get(i).getGeometryText();
            }else{
            }
        }

        String stPoint_data=stPoint.replace("[","");
        String stPoint_data1=stPoint_data.replace("]","");
        String[] st_point=stPoint_data1.split(",");
        double st_point_lat= Double.parseDouble(st_point[1]);
        double st_point_lnag= Double.parseDouble(st_point[0]);
        LatLng st_Point_vertex=new LatLng(st_point_lat,st_point_lnag);

        String endPoint_data=endPoint.replace("[","");
        String endPoint_data1=endPoint_data.replace("]","");
        String[] end_point=endPoint_data1.split(",");
        double end_point_lat= Double.parseDouble(end_point[1]);
        double end_point_lnag= Double.parseDouble(end_point[0]);
        LatLng end_Point_vertex=new LatLng(end_point_lat,end_point_lnag);
        double Distance_To_travelIn_Vertex=showDistance(currentGpsPosition,end_Point_vertex);
        String Distance_To_travelIn_Vertex_Convetred=String.format("%.0f", Distance_To_travelIn_Vertex);


        if (geometryTextimpValue.equals("-")) {

        } else {
            if(geometryTextimpValue!=null && !geometryTextimpValue.isEmpty()){
                String data = geometryTextimpValue + " " + Distance_To_travelIn_Vertex_Convetred + "Meters";
                Log.e("GROMETRY TEXT","GEOMETRY DIRECTION TEXT ----- "+data);
                //String data=" in "+ DitrectionDistance +" Meters "+ directionTextFinal;
                int speechStatus = textToSpeech.speak(data, TextToSpeech.QUEUE_FLUSH, null);
                if (speechStatus == TextToSpeech.ERROR) {
                    Log.e("TTS", "Error in converting Text to Speech!");
                }
                if(getActivity()!=null) {
                    LayoutInflater inflater1 = getActivity().getLayoutInflater();
                    @SuppressLint("WrongViewCast") final View layout = inflater1.inflate(R.layout.custom_toast, (ViewGroup) getActivity().findViewById(R.id.textView_toast));
                    TextView text = (TextView) layout.findViewById(R.id.textView_toast);

                    text.setText("" + geometryTextimpValue + " " + Distance_To_travelIn_Vertex_Convetred + "Meters");
                    ImageView image = (ImageView) layout.findViewById(R.id.image_toast);
                    if (geometryTextimpValue.contains("Take Right")) {
                        image.setImageResource(R.drawable.direction_right);
                    } else if (geometryTextimpValue.contains("Take Left")) {
                        image.setImageResource(R.drawable.direction_left);
                    }
                    new Handler(Looper.getMainLooper()).post(new Runnable() {
                        @Override
                        public void run() {
                            Toast toast = new Toast(getActivity().getApplicationContext());
                            toast.setDuration(Toast.LENGTH_LONG);
                            toast.setGravity(Gravity.TOP | Gravity.CENTER_HORIZONTAL, 0, 0);
                            toast.setGravity(Gravity.TOP, 0, 130);
                            toast.setView(layout);
                            toast.show();
                        }
                    });
                }
            }
        }

    }

    public void caclulateETA(final double TotalDistance, final LatLng sourcePosition, final LatLng currentGpsPosition, LatLng DestinationPosition){

        // Log.e("Total Distance","Total Distance"+ TotalDistanceInMTS);
        ETACalclator etaCalculator1=new ETACalclator();
        double resultTotalETA=etaCalculator1.cal_time(TotalDistanceInMTS, maxSpeed);
        final double resultTotalTimeConverted = DecimalUtils.round(resultTotalETA,0);
        //Log.e("resultTotalTime ","resultTotalTimeConverted ------- "+ resultTotalTimeConverted);

        double resultTravelledTimeConverted=0.0;
        // double resultNeedToTeavelTimeConverted=0.0;
        double resultNeedToTeavelTime=0.0;
        double EtaCrossedTime = 0.0;
        double EtaElapsed = 0.0;
        double resultTravelledTime=0.0;
        String etaCrossedFlag = "NO";
        if(vehicleSpeed==0.0){
            vehicleSpeed=10;
        }else {

            double travelledDistance = showDistance(sourcePosition, currentGpsPosition);
            String travelledDistanceInMTS = String.format("%.0f", travelledDistance);
            ETACalclator etaCalculator = new ETACalclator();
            resultTravelledTime = etaCalculator.cal_time(travelledDistance, vehicleSpeed);
            resultTravelledTimeConverted = DecimalUtils.round(resultTravelledTime, 0);


            double needToTravelDistance = TotalDistance - travelledDistance;
            String needToTravelDistanceInMTS = String.format("%.0f", needToTravelDistance);
            ETACalclator etaCalculator2 = new ETACalclator();
            resultNeedToTeavelTime = etaCalculator2.cal_time(needToTravelDistance, vehicleSpeed);
            resultNeedToTeavelTimeConverted = DecimalUtils.round(resultNeedToTeavelTime, 0);
        }
        if (resultTravelledTimeConverted > resultTotalTimeConverted) {
            etaCrossedFlag = "YES";
            EtaCrossedTime = resultTravelledTime - resultTotalTimeConverted;
            EtaElapsed = DecimalUtils.round(EtaCrossedTime, 0);
        } else {
            etaCrossedFlag = "NO";
        }

        time.append("Distance : ").append(TotalDistance +" Meters ").append("::").append("Total ETA : ").append(resultTotalETA +" SEC ").append("::").append(" Distance To Travel : ").append(resultNeedToTeavelTime +"Sec").append("::").append("Elapsed Time : ").append(EtaElapsed).append("::").append("currentGpsPosition : ").append(currentGpsPosition).append("\n");
        if(time.toString()!=null) {
            sendData(time.toString(), MapEvents.ALERTTYPE_2);
        }
    }
    @RequiresApi(api = Build.VERSION_CODES.JELLY_BEAN)
    public boolean VerifyRouteOutOfTrackConsequently(List<LatLng> edgeWithoutDuplicates,List<LatLng> RouteDeviationPointsForComparision){
        List<LatLng> EdgeWithoutDuplicates = removeDuplicates(edgeDataPointsList);
      //  List<LatLng> EdgeWithoutDuplicatesInRouteDeviationPoints = removeDuplicatesRouteDeviated(RouteDeviationPointsForComparision);
        checkPointsOfExistingRoutewithNewRoute(EdgeWithoutDuplicates,RouteDeviationPointsForComparision);
        Log.e("List Verification","List Verification commonPoints --  DATA "+ commonPoints.size());
        Log.e("List Verification","List Verification  new_unCommonPoints -- DATA "+ new_unCommonPoints.size());

        if(new_unCommonPoints.size()==0 ||new_unCommonPoints.size()<5){
          isContinuoslyOutOfTrack=true;

        }
    return isContinuoslyOutOfTrack;
    }
    @RequiresApi(api = Build.VERSION_CODES.JELLY_BEAN)
    public void MoveOutOfTrack(){
        animateCarMove(mPositionMarker,OldGPSPosition,currentGPSPosition,1000);
       // mPositionMarker.setPosition(currentGpsPosition);
       // mPositionMarker.setAnchor(0.5f,0.5f);
        currentLocationList.add(currentGpsPosition);
        float bearing= (float) bearingBetweenLocations(OldGPSPosition,currentGpsPosition);
        CameraPosition currentPlace = new CameraPosition.Builder()
                .target(currentGpsPosition)
                .bearing(bearing).tilt(65.5f).zoom(18)
                .build();
        mMap.animateCamera(CameraUpdateFactory.newCameraPosition(currentPlace), 1000, null);

        if (Build.VERSION.SDK_INT >= Build.VERSION_CODES.JELLY_BEAN) {
            if(OldGPSPosition!=null && currentGpsPosition!=null) {
                //verifyRouteDeviation(OldGPSPosition, currentGpsPosition, DestinationNode, routeDeviationDistance, null);
            }
        }
        if(isRouteDeviated==false) {
            PolylineOptions polylineOptions = new PolylineOptions();
            // polylineOptions.add(OldGPSPosition);
            polylineOptions.addAll(currentLocationList);
            Polyline polyline = mMap.addPolyline(polylineOptions);
            polylineOptions.color(Color.RED).width(30);
            mMap.addPolyline(polylineOptions);
            polyline.setJointType(JointType.ROUND);
        }
    }
    @RequiresApi(api = Build.VERSION_CODES.JELLY_BEAN)
    public double verifyDeviationCalculateDistance(final LatLng PrevousGpsPosition, final LatLng currentGpsPosition){
        double firstDeviatrionDistance=0.0;
        if (PrevousGpsPosition != null) {
            LatLng nearest_LatLng_deviation = GetNearestPointOnRoadFromGPS(PrevousGpsPosition, currentGpsPosition);
            firstDeviatrionDistance = showDistance(currentGpsPosition, nearest_LatLng_deviation);
        }
        Log.e("Route Deviation","ROUTE DEVIATION DISTANCE 1 st TIME ---- "+ firstDeviatrionDistance);
        return firstDeviatrionDistance;
    }
    @RequiresApi(api = Build.VERSION_CODES.JELLY_BEAN)
    public void verifyRouteDeviationTask(final LatLng PrevousGpsPosition, final LatLng currentGpsPosition, final LatLng DestinationPosition, int markDistance, final List<LatLng>EdgeWithoutDuplicates){
        Log.e("Route Deviation", "CURRENT GPS ----" + currentGpsPosition);
        Log.e("Route Deviation", " OLD GPS POSITION  ----" + PrevousGpsPosition);
        if (PrevousGpsPosition != null){
                String cgpsLat = String.valueOf(currentGpsPosition.latitude);
                String cgpsLongi = String.valueOf(currentGpsPosition.longitude);
                final String routeDiationPosition = cgpsLongi.concat(" ").concat(cgpsLat);
                Log.e("Route Deviation","routeDiationPosition   ######"+ routeDiationPosition);

                String destLatPos = String.valueOf(DestinationPosition.latitude);
                String destLongiPos = String.valueOf(DestinationPosition.longitude);
                final String destPoint = destLongiPos.concat(" ").concat(destLatPos);
                RouteDeviatedSourcePosition = new LatLng(Double.parseDouble(cgpsLat), Double.parseDouble(cgpsLongi));
                Log.e("Route Deviation","routeDiation SOURCE Position  ###### "+ RouteDeviatedSourcePosition);
                Log.e("returnedDistance", "RouteDiationPosition  ###### " + routeDiationPosition);
                if(getActivity()!=null) {
                    dialog = new ProgressDialog(getContext(), R.style.ProgressDialog);
                    dialog.setMessage("Fetching new Route");
                    dialog.setMax(100);
                    dialog.show();
                }
                if(getActivity()!=null){
                    getActivity().runOnUiThread(new Runnable() {
                        @Override
                        public void run() {
                            String MESSAGE = "";
                            GetRouteDetails(routeDiationPosition, destPoint);
                            if (RouteDeviationConvertedPoints != null && RouteDeviationConvertedPoints.size() > 0) {

                                List<LatLng> EdgeWithoutDuplicates = removeDuplicates(edgeDataPointsList);
                                List<LatLng> EdgeWithoutDuplicatesInRouteDeviationPoints = removeDuplicatesRouteDeviated(RouteDeviationPointsForComparision);
                                if(EdgeWithoutDuplicates!=null && EdgeWithoutDuplicatesInRouteDeviationPoints!=null) {
                                    checkPointsOfExistingRoutewithNewRoute(EdgeWithoutDuplicates,RouteDeviationPointsForComparision);
                                    Log.e("List Verification","List Verification commonPoints --  DATA "+ commonPoints.size());
                                    Log.e("List Verification","List Verification  new_unCommonPoints -- DATA "+ new_unCommonPoints.size());
                                    if(commonPoints.size()==0){
                                        if (mPositionMarker != null && mPositionMarker.isVisible() == true) {
                                            PolylineOptions polylineOptions = new PolylineOptions();
                                            // polylineOptions.add(OldGPSPosition);
                                            polylineOptions.addAll(RouteDeviationConvertedPoints);
                                            Polyline polyline = mMap.addPolyline(polylineOptions);
                                            polylineOptions.color(Color.RED).width(30);
                                            mMap.addPolyline(polylineOptions);
                                            polyline.setJointType(JointType.ROUND);
                                        }
                                    }
                                    else if(commonPoints.size()>0){
                                        Log.e("Route Deviation", " IS ROUTE VERIFY  ###### " + new_unCommonPoints.size());
                                        if(new_unCommonPoints.size()>5) {

                                            Log.e("Route Deviation", " IS ROUTE VERIFY  ###### " + " Route COINSIDENCE");
                                            if (mPositionMarker != null && mPositionMarker.isVisible() == true) {
                                                PolylineOptions polylineOptions = new PolylineOptions();
                                                // polylineOptions.add(OldGPSPosition);
                                                polylineOptions.addAll(new_unCommonPoints);
                                                Polyline polyline = mMap.addPolyline(polylineOptions);
                                                polylineOptions.color(Color.RED).width(30);
                                                mMap.addPolyline(polylineOptions);
                                                polyline.setJointType(JointType.ROUND);
                                           }
                                            LatLng cur_position=mPositionMarker.getPosition();
                                            String Route_st= String.valueOf(RouteDeviationConvertedPoints.get(0));
                                            Log.e("Route Deviation", "RouteDeviation_RouteSt_point " +  RouteDeviationConvertedPoints.get(0));
                                            Log.e("Route Deviation", "RouteDeviation_RouteSt_point " + Route_st);


                                            String Rt_st_pt=Route_st.replace("lat/lng: (","");
                                            String Rt_st_pt1=Rt_st_pt.replace(")","");
                                            String[]Rt_st_pt1Points =Rt_st_pt1.split(",");
                                            double lat= Double.parseDouble(Rt_st_pt1Points[0]);
                                            double longi= Double.parseDouble(Rt_st_pt1Points[1]);
                                            LatLng RouteDeviation_RouteSt_point=new LatLng(lat,longi);
                                            Log.e("Route Deviation", "RouteDeviation_RouteSt_point " + Route_st);

                                           // drawMarkerWithCircle(RouteDeviation_RouteSt_point,20);
                                            double rd_ditance=distFrom(RouteDeviation_RouteSt_point.latitude,RouteDeviation_RouteSt_point.longitude,cur_position.latitude,cur_position.longitude);
                                            Log.e("Route Deviation", "RouteDeviation_RouteSt_point Distance Buffer" + rd_ditance);
                                            if(rd_ditance<20) {
                                                Log.e("Route Deviation", " Inside Route Deviation Buffer " + rd_ditance);
                                                isRouteDeviated=true;
                                                isContinuoslyOutOfTrack=false;
                                                LatLng markerPosition=mPositionMarker.getPosition();
                                                Log.e("Route Deviation", "RouteDeviation_RouteSt_point Distance Buffer --Marker _Position" + markerPosition);


                                                    LatLng compare_pt = new_unCommonPoints.get(0);
                                                    Log.e("Route Deviation", " IS ROUTE VERIFY   ###### Compare _point" + compare_pt);
                                                    double compare_distance_pt = distFrom(markerPosition.latitude, markerPosition.longitude, compare_pt.latitude, compare_pt.longitude);

                                                    drawMarkerWithCircle(compare_pt, 40);
                                                    if (compare_distance_pt < 20) {
                                                        LayoutInflater inflater1 = getActivity().getLayoutInflater();
                                                        @SuppressLint("WrongViewCast") View layout = inflater1.inflate(R.layout.custom_toast, (ViewGroup) getActivity().findViewById(R.id.textView_toast));
                                                        TextView text = (TextView) layout.findViewById(R.id.textView_toast);
                                                        text.setText("Route Deviated");
                                                        Toast toast = new Toast(getActivity().getApplicationContext());
                                                        toast.setDuration(Toast.LENGTH_LONG);
                                                        toast.setGravity(Gravity.TOP | Gravity.CENTER_HORIZONTAL, 0, 0);
                                                        toast.setGravity(Gravity.TOP, 0, 150);
                                                        toast.setView(layout);
                                                        toast.show();
                                                        StringBuilder routeDeviatedAlert = new StringBuilder();
                                                        routeDeviatedAlert.append("ROUTE DEVIATED" + " RouteDeviatedSourcePosition : " + RouteDeviatedSourcePosition);
                                                        sendData(MapEvents.ALERTVALUE_3, MapEvents.ALERTTYPE_3);
                                                    }


                                                MoveWithGpsPointInRouteDeviatedPoints(currentGpsPosition);
                                            }
                                            }else{

                                            }
                                            /*
                                             LatLng cur_position=mPositionMarker.getPosition();
                                                String Route_end= String.valueOf(RouteDeviationConvertedPoints.get(RouteDeviationConvertedPoints.size()-1));
                                                Log.e("Route Deviation", "RouteDeviation_RouteSt_point " +  RouteDeviationConvertedPoints.get(RouteDeviationConvertedPoints.size()-1));
                                                Log.e("Route Deviation", "RouteDeviation_RouteSt_point " + Route_end);


                                                String Rt_end_pt=Route_end.replace("lat/lng: (","");
                                                String Rt_end_pt1=Rt_end_pt.replace(")","");
                                                String[]Rt_end_pt1Points =Rt_end_pt1.split(",");
                                                double lat= Double.parseDouble(Rt_end_pt1Points[0]);
                                                double longi= Double.parseDouble(Rt_end_pt1Points[1]);
                                                LatLng RouteDeviation_RouteEnd_point=new LatLng(lat,longi);
                                                Log.e("Route Deviation", "RouteDeviation_RouteSt_point " + Rt_end_pt);

                                                drawMarkerWithCircle(RouteDeviation_RouteEnd_point,20);
                                                double rd_ditance=distFrom(RouteDeviation_RouteEnd_point.latitude,RouteDeviation_RouteEnd_point.longitude,cur_position.latitude,cur_position.longitude);
                                                Log.e("Route Deviation", "RouteDeviation_RouteSt_point Distance Buffer" + rd_ditance);
                                                if(rd_ditance<20) {
                                                    Log.e("Route Deviation", " Inside Route Deviation Buffer " + rd_ditance);
                                                    isRouteDeviated=false;

                                                }else{

                                                }
                                             */
                                    }
                                    else if(new_unCommonPoints.size()==0){
                                        Log.e("List Verification","List Verification  new_unCommonPoints -- DATA "+ " OLD ROUTE");

                                    }

                                }

                            }

                        }
                    });
            }
        }
    }
    /*

    @RequiresApi(api = Build.VERSION_CODES.JELLY_BEAN)
    public boolean verifyRouteDeviation(final LatLng PrevousGpsPosition, final LatLng currentGpsPosition, final LatLng DestinationPosition, int markDistance, final List<LatLng>EdgeWithoutDuplicates) {

             // After getting current gps verifing in the  radius of
             // in the routebetween the Previous and current gps position
             // if Route deviation exists it shows the message Route Deviated it will get route from the service and plot route on map
             //  otherwise continue with the existed route

        Log.e("Route Deviation", "CURRENT GPS ----" + currentGpsPosition);
        Log.e("Route Deviation", " OLD GPS POSITION  ----" + PrevousGpsPosition);
        if (PrevousGpsPosition != null){

            // GetNearestPointOnRoadFromGPS(PrevousGpsPosition,currentGpsPosition)-- in this method PrevousGpsPosition is not using any where,
            //  we are sending it for
           //  handling parameter exception only ---

            LatLng nearest_LatLng_deviation= GetNearestPointOnRoadFromGPS(PrevousGpsPosition,currentGpsPosition);
            double returnedDistance = showDistance(currentGpsPosition, nearest_LatLng_deviation);
            Log.e("Route Deviation","ROUTE DEVIATION DISTANCE RETURNED ---- "+returnedDistance);
            if(returnedDistance >routeDeviationDistance){
                String cgpsLat = String.valueOf(currentGpsPosition.latitude);
                String cgpsLongi = String.valueOf(currentGpsPosition.longitude);
                final String routeDiationPosition = cgpsLongi.concat(" ").concat(cgpsLat);
                Log.e("Route Deviation","routeDiationPosition   ######"+ routeDiationPosition);

                String destLatPos = String.valueOf(DestinationPosition.latitude);
                String destLongiPos = String.valueOf(DestinationPosition.longitude);
                final String destPoint = destLongiPos.concat(" ").concat(destLatPos);
                RouteDeviatedSourcePosition = new LatLng(Double.parseDouble(cgpsLat), Double.parseDouble(cgpsLongi));
                Log.e("Route Deviation","routeDiation SOURCE Position  ###### "+ RouteDeviatedSourcePosition);
                Log.e("returnedDistance", "RouteDiationPosition  ###### " + routeDiationPosition);
                //   Log.e("returnedDistance", "Destination Position --------- " + destPoint);
               // DestinationPosition = new LatLng(destLat, destLng);
                dialog = new ProgressDialog(getActivity(), R.style.ProgressDialog);
                dialog.setMessage("Fetching new Route");
                dialog.setMax(100);
               dialog.show();
                getActivity().runOnUiThread(new Runnable() {
                    @Override
                    public void run() {
                        String MESSAGE = "";
                        GetRouteDetails(routeDiationPosition, destPoint);
                        if (RouteDeviationConvertedPoints != null && RouteDeviationConvertedPoints.size() > 0) {
                            List<LatLng> EdgeWithoutDuplicates = removeDuplicates(edgeDataPointsList);
                            List<LatLng> EdgeWithoutDuplicatesInRouteDeviationPoints = removeDuplicatesRouteDeviated(RouteDeviationPointsForComparision);
                            if(EdgeWithoutDuplicates!=null && EdgeWithoutDuplicatesInRouteDeviationPoints!=null) {
                                checkPointsOfExistingRoutewithNewRoute(EdgeWithoutDuplicates,RouteDeviationPointsForComparision);
                                Log.e("List Verification","List Verification commonPoints --  DATA "+ commonPoints.size());
                                Log.e("List Verification","List Verification  new_unCommonPoints -- DATA "+ new_unCommonPoints.size());
                                if(commonPoints.size()==0){
                                    if (mPositionMarker != null && mPositionMarker.isVisible() == true) {
                                        PolylineOptions polylineOptions = new PolylineOptions();
                                        // polylineOptions.add(OldGPSPosition);
                                        polylineOptions.addAll(RouteDeviationConvertedPoints);
                                        Polyline polyline = mMap.addPolyline(polylineOptions);
                                        polylineOptions.color(Color.RED).width(30);
                                        mMap.addPolyline(polylineOptions);
                                        polyline.setJointType(JointType.ROUND);
                                    }
                                   // isRouteDeviated = true;
                                   // MoveWithGpsPointInRouteDeviatedPoints(currentGpsPosition);
                                    //

                                    Log.e("List Verification","List Verification  new_unCommonPoints -- DATA "+ "NEW ROUTE");
                                    Log.e("Route Deviation", " IS ROUTE VERIFY  ###### " + " Route NOT EQUAL");
                                    isRouteDeviated = true;
                                    LayoutInflater inflater1 = getActivity().getLayoutInflater();
                                    @SuppressLint("WrongViewCast") View layout = inflater1.inflate(R.layout.custom_toast, (ViewGroup) getActivity().findViewById(R.id.textView_toast));
                                    TextView text = (TextView) layout.findViewById(R.id.textView_toast);

                                    text.setText("Route Deviated");

                                    Toast toast = new Toast(getActivity().getApplicationContext());
                                    toast.setDuration(Toast.LENGTH_LONG);
                                    toast.setGravity(Gravity.TOP | Gravity.CENTER_HORIZONTAL, 0, 0);
                                    toast.setGravity(Gravity.TOP, 0, 150);
                                    toast.setView(layout);
                                    toast.show();
                                    StringBuilder routeDeviatedAlert = new StringBuilder();
                                    routeDeviatedAlert.append("ROUTE DEVIATED" + "RouteDeviatedSourcePosition : " + RouteDeviatedSourcePosition);
                                    sendData(MapEvents.ALERTVALUE_3, MapEvents.ALERTTYPE_3);
                                    if (mPositionMarker != null) {
                                        mPositionMarker.remove();
                                        Log.e("REMOVING MARKER", "REMOVING MARKER");
                                    }
                                    mPositionMarker = mMap.addMarker(new MarkerOptions()
                                            .position(currentGpsPosition)
                                            .title("currentLocation")
                                            .anchor(0.5f, 0.5f)
                                            .flat(true)
                                            .icon(bitmapDescriptorFromVector(getContext(), R.drawable.gps_transperent_98)));


                                    CameraUpdate center =
                                            CameraUpdateFactory.newLatLng(currentGpsPosition);
                                    CameraUpdate zoom = CameraUpdateFactory.zoomTo(22);
                                    mMap.moveCamera(center);
                                    mMap.animateCamera(zoom);


                                }
                                else if(commonPoints.size()>0){
                                    Log.e("Route Deviation", " IS ROUTE VERIFY  ###### " + " Route COINSIDENCE");
                                    if (mPositionMarker != null && mPositionMarker.isVisible() == true) {
                                        PolylineOptions polylineOptions = new PolylineOptions();
                                        // polylineOptions.add(OldGPSPosition);
                                        polylineOptions.addAll(new_unCommonPoints);
                                        Polyline polyline = mMap.addPolyline(polylineOptions);
                                        polylineOptions.color(Color.RED).width(30);
                                        mMap.addPolyline(polylineOptions);
                                        polyline.setJointType(JointType.ROUND);
                                    }
                                   //MoveWithGpsPointInRouteDeviatedPoints(currentGpsPosition);
                                   isRouteDeviated = true;
                                    LayoutInflater inflater1 = getActivity().getLayoutInflater();
                                    @SuppressLint("WrongViewCast") View layout = inflater1.inflate(R.layout.custom_toast, (ViewGroup) getActivity().findViewById(R.id.textView_toast));
                                    TextView text = (TextView) layout.findViewById(R.id.textView_toast);

                                    text.setText("Route Deviated");

                                    Toast toast = new Toast(getActivity().getApplicationContext());
                                    toast.setDuration(Toast.LENGTH_LONG);
                                    toast.setGravity(Gravity.TOP | Gravity.CENTER_HORIZONTAL, 0, 0);
                                    toast.setGravity(Gravity.TOP, 0, 150);
                                    toast.setView(layout);
                                    toast.show();
                                }
                                else if(new_unCommonPoints.size()==0){
                                    Log.e("List Verification","List Verification  new_unCommonPoints -- DATA "+ " OLD ROUTE");

                                }
                            }


                        }


                    }
                });

            }

        }else{

        }
        return isRouteDeviated;
    }

     */


    public void  checkPointsOfExistingRoutewithNewRoute(List<LatLng> edgeWithoutDuplicates,List<LatLng> RouteDeviationPointsForComparision){
        List<LatLng> EdgeWithoutDuplicatesInRouteDeviationPoints = removeDuplicatesRouteDeviated(RouteDeviationPointsForComparision);
        for(int k=0;k< EdgeWithoutDuplicatesInRouteDeviationPoints.size();k++) {
            // Log.e("Route Deviated----", "EdgeWithoutDuplicatesInRouteDeviationPoints ------- " + EdgeWithoutDuplicatesInRouteDeviationPoints.get(k));
        }
        for(int k=0;k< edgeWithoutDuplicates.size();k++) {
            //  Log.e("Route Deviated----", "edgeWithoutDuplicates ------- " + edgeWithoutDuplicates.get(k));
        }
        commonPoints =new ArrayList<LatLng>();
        commonPoints.clear();
        new_unCommonPoints=new ArrayList<LatLng>();
        new_unCommonPoints.clear();
        String elementOfList1="";
        String elementOfList2="";
        String element1SubElement="";
        String element2SubElement="";
        for(int i=0;i<EdgeWithoutDuplicatesInRouteDeviationPoints.size();i++){
            elementOfList1=EdgeWithoutDuplicatesInRouteDeviationPoints.get(i).toString();
            element1SubElement = elementOfList1.substring(0,24);


            for(int j=0;j<edgeWithoutDuplicates.size();j++){
                elementOfList2=edgeWithoutDuplicates.get(j).toString();
                element2SubElement=elementOfList2.substring(0,24);
                if(element1SubElement.equals(element2SubElement)){
                    // three=new ArrayList<>();
                    String ElementData=elementOfList1.replace("lat/lng: (","");
                    String ElementData1=ElementData.replace(")","");
                    String[]Elements =ElementData1.split(",");
                    double lat= Double.parseDouble(Elements[0]);
                    double longi= Double.parseDouble(Elements[1]);
                    LatLng commonData=new LatLng(longi,lat);
                    commonPoints.add(commonData);
                }

            }
            String ElementData=elementOfList1.replace("lat/lng: (","");
            //Log.e("List Verification","List Verification commonPoints --  DATA "+ ElementData);
            String ElementData1=ElementData.replace(")","");
            // Log.e("List Verification","List Verification commonPoints --  DATA "+ ElementData1);
            String[]Elements =ElementData1.split(",");
            // Log.e("List Verification","List Verification commonPoints --  DATA "+ Elements);
            double lat= Double.parseDouble(Elements[0]);
            // Log.e("List Verification","List Verification commonPoints --  DATA "+ lat);
            double longi= Double.parseDouble(Elements[1]);
            // Log.e("List Verification","List Verification commonPoints --  DATA "+ longi);
            LatLng commonData1=new LatLng(longi,lat);
            new_unCommonPoints.add(commonData1);
            new_unCommonPoints.removeAll(commonPoints);
        }
            /*
         boolean isEqual = EdgeWithoutDuplicatesInRouteDeviationPoints.retainAll(edgeWithoutDuplicates);
         Log.e("Route Deviation"," List Retains FLAG" +isEqual);
         Log.e("Route Deviation"," List Retains ELEMENTS--" + EdgeWithoutDuplicatesInRouteDeviationPoints);

        // boolean isEqual = edgeWithoutDuplicates.equals(RouteDeviationConvertedPoints);      //false
         System.out.println(isEqual);
         */

    }
    @RequiresApi(api = Build.VERSION_CODES.JELLY_BEAN)
    public void MoveWithGpsPointInRouteDeviatedPoints(LatLng currentGpsPosition){
        LatLng FirstCordinate = null,SecondCordinate=null;
        LatLng  OldGpsRouteDeviation=null;
        if(RouteDeviationConvertedPoints!=null) {

            StringBuilder routeDeviatedAlert = new StringBuilder();
            routeDeviatedAlert.append("ROUTE DEVIATED" + "RouteDeviatedSourcePosition : " + RouteDeviatedSourcePosition);
            sendData(MapEvents.ALERTVALUE_3, MapEvents.ALERTTYPE_3);


            Log.e("Route Deviated", "Route Deviated EdgesList ------- " + RouteDeviationConvertedPoints.size());
            Log.e("Route Deviated", "Current GPS position ------- " + currentGpsPosition);
            List<LatLng> EdgeWithoutDuplicatesInRouteDeviationPoints = removeDuplicatesRouteDeviated(RouteDeviationConvertedPoints);
            for (int k = 0; k < EdgeWithoutDuplicatesInRouteDeviationPoints.size(); k++) {
                //Log.e("Route Deviated----", "EdgeWithoutDuplicatesInRouteDeviationPoints ------- " + EdgeWithoutDuplicatesInRouteDeviationPoints.get(k));
            }

            if (EdgeWithoutDuplicatesInRouteDeviationPoints != null && EdgeWithoutDuplicatesInRouteDeviationPoints.size() > 0) {
                if(nearestPositionPoint!=null) {
                    OldGpsRouteDeviation = nearestPositionPoint;
                }
                List distancesInDeviation = new ArrayList();
                HashMap<String, LatLng> distancesMapInRouteDeviation = new HashMap<String, LatLng>();
                for (int epList = 0; epList < EdgeWithoutDuplicatesInRouteDeviationPoints.size(); epList++) {
                    LatLng PositionMarkingPoint = EdgeWithoutDuplicatesInRouteDeviationPoints.get(epList);
                    //  Log.e("Route Deviation", " Route Deviation PositionMarking Point" + PositionMarkingPoint);
                    double distance = distFrom(PositionMarkingPoint.longitude, PositionMarkingPoint.latitude, currentGpsPosition.longitude, currentGpsPosition.latitude);
                    distancesMapInRouteDeviation.put(String.valueOf(distance), PositionMarkingPoint);
                    distancesInDeviation.add(distance);
                    Collections.sort(distancesInDeviation);
                }
                for (int k = 0; k < distancesInDeviation.size(); k++) {
                    // Log.e("Route Deviation", " distancesInDeviation" + distancesInDeviation.get(k));
                }
                // Log.e("Route Deviation", " distancesInDeviation" + distancesInDeviation);
                //  Log.e("Route Deviation", " distancesMapInRouteDeviation" + distancesMapInRouteDeviation);
                String firstShortestDistance = String.valueOf(distancesInDeviation.get(0));
                String secondShortestDistance = String.valueOf(distancesInDeviation.get(1));
                boolean answerFirst = distancesMapInRouteDeviation.containsKey(firstShortestDistance);
                if (answerFirst) {
                    System.out.println("The list contains " + firstShortestDistance);
                    FirstCordinate = distancesMapInRouteDeviation.get(firstShortestDistance);
                    //  Log.e("Route Deviation", " FIRST Cordinate  From Route deviation" + FirstCordinate);
                    // key= String.valueOf(getKeysFromValue(EdgeWithoutDuplicatesInRouteDeviationPoints,FirstCordinate));
                    // distanceKey= String.valueOf(getKeysFromValue(AllPointEdgeDistaces,FirstCordinate));
                    for(int i=0;i<geometryRouteDeviatedEdgesData.size();i++){
                        GeometryT geometry=geometryRouteDeviatedEdgesData.get(i);
                        String routeDeviationTextPoint= geometry.getPositionMarkingPoint();
                        // Log.e("Route Deviation", " ST_VERTEX From Route deviation" + routeDeviationTextPoint);

                        if(routeDeviationTextPoint.equals(FirstCordinate.toString())){
                            int index = geometryRouteDeviatedEdgesData.indexOf(routeDeviationTextPoint);
                            st_vertex=geometry.getStartPoint();
                            end_vertex=geometry.getEndPoint();
                            directionTextRouteDeviation=geometry.getGeometryText();
                            Log.e("DirectionText","Direction Text Deviation"+directionTextRouteDeviation);

                        }
                    }

                } else {
                    System.out.println("The list does not contains " + "FALSE");
                }
                boolean answerSecond = distancesMapInRouteDeviation.containsKey(secondShortestDistance);
                if (answerSecond) {
                    System.out.println("The list contains " + secondShortestDistance);
                    SecondCordinate = distancesMapInRouteDeviation.get(secondShortestDistance);
                    //  Log.e("Route Deviation", " SECOND Cordinate  From Route deviation" + SecondCordinate);
                    // key= String.valueOf(getKeysFromValue(EdgeWithoutDuplicatesInRouteDeviationPoints,FirstCordinate));
                    // distanceKey= String.valueOf(getKeysFromValue(AllPointEdgeDistaces,FirstCordinate));
                } else {
                    System.out.println("The list does not contains " + "FALSE");
                }
                //  Log.e("Route Deviation", " currentGpsPosition From Route deviation " + currentGpsPosition);
                //  Log.e("Route Deviation", " FirstCordinate From Route deviation " + FirstCordinate);
                //   Log.e("Route Deviation", " Second Cordinate From Route deviation " + SecondCordinate);

                nearestPositionPoint = findNearestPoint(currentGpsPosition, FirstCordinate, SecondCordinate);
                //  Log.e("Route Deviation", " NEAREST POSITION From Route deviation " + nearestPositionPoint);
                OldNearestGpsList.add(nearestPositionPoint);

            }
            Log.e("Route Deviation", " OldGps POSITION From Route deviation " + OldGpsRouteDeviation);
            Log.e("Route Deviation", " NEAREST POSITION From Route deviation " + nearestPositionPoint);
            nearestPointValuesList.add(nearestPositionPoint);
            double distance=distFrom(currentGpsPosition.latitude,currentGpsPosition.longitude,nearestPositionPoint.latitude,nearestPositionPoint.longitude);
          //  if(distance<routeDeviationDistance) {
                if (OldGpsRouteDeviation != null && nearestPositionPoint != null) {
                    float bearing = (float) bearingBetweenLocations(OldGpsRouteDeviation, nearestPositionPoint); //correct method to change orientation of map
                    if (mPositionMarker == null) {
                        mPositionMarker = mMap.addMarker(new MarkerOptions()
                                .position(currentGpsPosition)
                                .title("currentLocation")
                                .anchor(0.5f, 0.5f)
                                .rotation(bearing)
                                .icon(bitmapDescriptorFromVector(getContext(), R.drawable.gps_transperent_98))
                                .flat(true));
                    } else {
                        if (islocationControlEnabled == false) {
                            animateCarMove(mPositionMarker, OldGpsRouteDeviation, nearestPositionPoint, 1000);
                            int height = 0;
                            if (getView() != null) {
                                height = getView().getMeasuredHeight();
                            }
                            Projection p = mMap.getProjection();
                            Point bottomRightPoint = p.toScreenLocation(p.getVisibleRegion().nearRight);
                            Point center = new Point(bottomRightPoint.x / 2, bottomRightPoint.y / 2);
                            Point offset = new Point(center.x, (center.y + (height / 4)));
                            LatLng centerLoc = p.fromScreenLocation(center);
                            LatLng offsetNewLoc = p.fromScreenLocation(offset);
                            double offsetDistance = SphericalUtil.computeDistanceBetween(centerLoc, offsetNewLoc);
                            LatLng shadowTgt = SphericalUtil.computeOffset(nearestPositionPoint, offsetDistance, bearing);
                            CaluculateETAInRouteDeviationDirection(TotalRouteDeviatedDistanceInMTS, RouteDeviatedSourcePosition, currentGpsPosition, DestinationNode);
                            AlertDestination(currentGpsPosition);
                            if (bearing > 0.0) {
                                CameraPosition currentPlace = new CameraPosition.Builder()
                                        .target(shadowTgt)
                                        .bearing(bearing).tilt(65.5f).zoom(18)
                                        .build();
                                mMap.animateCamera(CameraUpdateFactory.newCameraPosition(currentPlace), 1000, null);
                            } else {

                            }
                        } else if (islocationControlEnabled == true) {

                            animateCarMoveNotUpdateMarker(mPositionMarker, OldGpsRouteDeviation, nearestPositionPoint, 1000);

                        }

                    }


                }

        }
    }

    private void GetRouteDetails(final String deviationPoint, final String newDestinationPoint){
        try{
            // Log.e("Deviation Point","Deviation Point" + deviationPoint);
            // Log.e("newDestinationPoint","newDestinationPoint" + newDestinationPoint);
            getActivity().runOnUiThread(new Runnable() {
                @Override
                public void run() {
                    if (Build.VERSION.SDK_INT > 9) {
                        StrictMode.ThreadPolicy policy =
                                new StrictMode.ThreadPolicy.Builder().permitAll().build();
                        StrictMode.setThreadPolicy(policy);
                        try {
                            // String httprequest = "http://202.53.11.74/dtnavigation/api/routing/routenavigate";
                            //  Log.e("HTTP REQUEST","HTTP REQUEST"+httprequest);
                            String FeatureResponse = HttpPost(routeDeviatedDT_URL,deviationPoint,newDestinationPoint);
                            //  Log.e("HTTP REQUEST","HTTP REQUEST"+ FeatureResponse);
                            JSONObject jsonObject = null;
                            try {
                                if(FeatureResponse!=null){
                                    String delQuery = "DELETE  FROM " + GeometryT.TABLE_NAME;
                                    sqlHandler.executeQuery(delQuery.toString());
                                    //   Log.e("DelQuery","DelQuery"+delQuery);
                                    jsonObject = new JSONObject(FeatureResponse);
                                    String ID = String.valueOf(jsonObject.get("$id"));
                                    // MESSAGE = jsonObject.getString("Message");
                                    String Status = jsonObject.getString("Status");
                                    double TotalDistance = jsonObject.getDouble("TotalDistance");
                                    TotalRouteDeviatedDistanceInMTS = jsonObject.getDouble("TotalDistance");
                                    JSONArray jSonRoutes = new JSONArray(jsonObject.getString("Route"));
                                    PolylineOptions polylineOptions = new PolylineOptions();

                                    polylineOptions.add(OldGPSPosition);
                                    PointBeforeRouteDeviation=new LatLng(OldGPSPosition.latitude,OldGPSPosition.longitude);
                                    Polyline polyline = null;
                                    RouteDeviationConvertedPoints=new ArrayList<LatLng>();
                                    RouteDeviationPointsForComparision=new ArrayList<LatLng>();
                                    geometryRouteDeviatedEdgesData=new ArrayList<GeometryT>();
                                    for (int i = 0; i < jSonRoutes.length(); i++) {
                                        List deviationPoints=new ArrayList();
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
                                            deviationPoints.add(jSonLegs.get(j));

                                        }
                                        //   Log.e("DEVIATION POINTS","DEVIATION POINTS"+deviationPoints.size());
                                        String  stPoint=String.valueOf(jSonLegs.get(0));
                                        stPoint=stPoint.replace("[","");
                                        stPoint=stPoint.replace("]","");
                                        String [] firstPoint=stPoint.split(",");
                                        Double stPointLat= Double.valueOf(firstPoint[0]);
                                        Double stPointLongi= Double.valueOf(firstPoint[1]);
                                        LatLng stVertex=new LatLng(stPointLongi,stPointLat);

                                        StringBuilder query = new StringBuilder("INSERT INTO ");
                                        query.append(GeometryT.TABLE_NAME).append("(edgeNo,distanceInVertex,startPoint,allPoints,geometryText,endPoint) values (")
                                                .append("'").append(EdgeNo).append("',")
                                                .append("'").append("distanceInKM").append("',")
                                                .append("'").append(jSonLegs.get(0)).append("',")
                                                .append("'").append(deviationPoints).append("',")
                                                .append("'").append(GeometryText).append("',")
                                                .append("'").append(jSonLegs.get(jSonLegs.length()-1)).append("')");
                                        sqlHandler.executeQuery(query.toString());
                                        // Log.e("INSERTION QUERY","INSERTION QUERY ----- "+ query);
                                        sqlHandler.closeDataBaseConnection();
                                        for (int p = 0; p < deviationPoints.size(); p++) {

                                            String listItem = deviationPoints.get(p).toString();
                                            listItem = listItem.replace("[", "");
                                            listItem = listItem.replace("]", "");
                                            String[] subListItem = listItem.split(",");
                                            Double y = Double.valueOf(subListItem[0]);
                                            Double x = Double.valueOf(subListItem[1]);
                                            StringBuilder sb=new StringBuilder();
                                            LatLng latLng = new LatLng(x, y);
                                            RouteDeviationConvertedPoints.add(latLng);
                                            LatLng reversePoint= new LatLng(y, x);
                                            RouteDeviationPointsForComparision.add(reversePoint);
                                            //Log.e("RouteDeviation","RouteDeviationConvertedPoints"+RouteDeviationConvertedPoints.size());

                                            GeometryT edgeRouteDeviatedPointData = new GeometryT(stPoint,jSonLegs.get(jSonLegs.length()-1).toString(),String.valueOf(latLng),GeometryText,"");
                                            geometryRouteDeviatedEdgesData.add(edgeRouteDeviatedPointData);
                                        }

                                        // Log.e("INSERTION QUERY","RouteDeviationConvertedPoints----- "+ RouteDeviationConvertedPoints);
                                        MarkerOptions markerOptions = new MarkerOptions();

                                        for (int k = 0; k < RouteDeviationConvertedPoints.size(); k++) {
                                            if(polylineOptions!=null && mMap!=null) {
                                                // markerOptions.position(RouteDeviationConvertedPoints.get(k));
                                               // Log.e("INSERTION QUERY","RouteDeviationConvertedPoints----- "+ RouteDeviationConvertedPoints.get(k));
                                                markerOptions.title("Position");
                                            }
                                        }
                                    }

                                }
                            } catch (JSONException e) {
                                e.printStackTrace();
                            }
                        }catch (Exception ex){

                        }
                        dialog.dismiss();
                    }
                }
            });
        }catch(Exception e){
            e.printStackTrace();
        }
        dialog.dismiss();
    }
    private String HttpPost(String myUrl,String latLng1,String latLng2) throws IOException, JSONException {
        StringBuilder sb = new StringBuilder();
        String LoginResponse = "";
        String result = "";
        URL url = new URL(myUrl);
        Log.v("URL ", " URL: " + url);
        HttpURLConnection conn = (HttpURLConnection) url.openConnection();
        conn.setRequestMethod("POST");
        conn.setRequestProperty("Content-Type", "application/json");
        conn.setRequestProperty("Accept", "text/plain");
        JSONObject jsonObject = buidJsonObject(latLng1,latLng2);
        // Log.e("JSON OBJECT","JSON OBJECT ------- "+jsonObject);
        setPostRequestContent(conn, jsonObject);
        conn.connect();
        result = conn.getResponseMessage();
        if (conn.getResponseCode() != 200) {

        } else {
            BufferedReader br = new BufferedReader(new InputStreamReader((conn.getInputStream())));
            String output = null;
            //   System.out.println("Output from Server .... \n");
            while ((output = br.readLine()) != null) {
                System.out.println(output);
                LoginResponse = sb.append(output).append(" ").toString();

            }
        }
        conn.disconnect();
        return LoginResponse;
    }

    private JSONObject buidJsonObject(String latLng1,String latLng2) throws JSONException {
        JSONObject buidJsonObject = new JSONObject();
        buidJsonObject.accumulate("UserData", buidJsonObject1());
        buidJsonObject.accumulate("StartNode", latLng1);
        buidJsonObject.accumulate("EndNode", latLng2);
        return buidJsonObject;
    }

    private JSONObject buidJsonObject1() throws JSONException {
        JSONObject buidJsonObject1 = new JSONObject();
        buidJsonObject1.accumulate("username", "admin");
        buidJsonObject1.accumulate("password", "admin");
        buidJsonObject1.accumulate("License", AuthorisationKey);

        return buidJsonObject1;
    }

    private void setPostRequestContent(HttpURLConnection conn,
                                       JSONObject jsonObject) throws IOException {
        OutputStream os = conn.getOutputStream();
        BufferedWriter writer = new BufferedWriter(new OutputStreamWriter(os, "UTF-8"));
        writer.write(jsonObject.toString());
        // Log.i(LoginActivity.class.toString(), jsonObject.toString());
        writer.flush();
        writer.close();
        os.close();
    }


    private List<LatLng> removeDuplicatesRouteDeviated(List<LatLng> EdgeWithoutDuplicatesInRouteDeviationPoints)
    {
        int count = RouteDeviationConvertedPoints.size();

        for (int i = 0; i < count; i++)
        {
            for (int j = i + 1; j < count; j++)
            {
                if (RouteDeviationConvertedPoints.get(i).equals(RouteDeviationConvertedPoints.get(j)))
                {
                    RouteDeviationConvertedPoints.remove(j--);
                    count--;
                }
            }
        }
        return EdgeWithoutDuplicatesInRouteDeviationPoints;
    }

    public static void animateMarker( final LatLng startPosition,final LatLng destination, final Marker marker) {
        if (marker != null) {
            // final LatLng startPosition = marker.getPosition();
            final LatLng endPosition = new LatLng(destination.latitude, destination.longitude);

            final float startRotation = marker.getRotation();

            final LatLngInterpolator latLngInterpolator = new LatLngInterpolator.LinearFixed();
            ValueAnimator valueAnimator = ValueAnimator.ofFloat(0, 1);
            valueAnimator.setDuration(2000); // duration 1 second
            valueAnimator.setInterpolator(new LinearInterpolator());
            valueAnimator.addUpdateListener(new ValueAnimator.AnimatorUpdateListener() {
                @Override public void onAnimationUpdate(ValueAnimator animation) {
                    try {
                        float v = animation.getAnimatedFraction();
                        float bearing =(float) getAngle(startPosition,destination);
                        LatLng newPosition = latLngInterpolator.interpolate(v, startPosition, endPosition);
                        marker.setPosition(newPosition);
                        marker.setRotation(bearing);
                    } catch (Exception ex) {
                        // I don't care atm..
                    }
                }
            });

            valueAnimator.start();
        }
    }
    private void drawMarkerWithCircle(LatLng gpsPosition, double radius){
        CircleOptions circleOptions = new CircleOptions().center(gpsPosition).radius(radius).fillColor(Color.parseColor("#2271cce7")).strokeColor(Color.parseColor("#2271cce7")).strokeWidth(3);
        mCircle = mMap.addCircle(circleOptions);

    }
    /*
 public static LatLng computeOffset(LatLng from,
                                    double distance,
                                    double heading){
    return  LatLng;
 }

     */
    public void AlertDestination(LatLng currentGpsPosition){
        //  int GpsIndex=OldNearestGpsList.indexOf(nearestPositionPoint);
        drawMarkerWithCircle(DestinationNode,10);
        double distanceAtLast = distFrom(currentGpsPosition.latitude, currentGpsPosition.longitude, mCircle.getCenter().latitude,  mCircle.getCenter().longitude);
        Log.e("LAST DISTANCE"," LAST DISTANCE @@@@@@@@@@@@@@@@@@@@ "+ distanceAtLast);
        if (distanceAtLast < mCircle.getRadius()) {
             /*   if (ActivityCompat.checkSelfPermission(getContext(), ACCESS_FINE_LOCATION) != PackageManager.PERMISSION_GRANTED && ActivityCompat.checkSelfPermission(getContext(), Manifest.permission.ACCESS_COARSE_LOCATION) != PackageManager.PERMISSION_GRANTED) {
                    // TODO: Consider calling
                    //    ActivityCompat#requestPermissions
                    // here to request the missing permissions, and then overriding
                    //   public void onRequestPermissionsResult(int requestCode, String[] permissions,
                    //                                          int[] grantResults)
                    // to handle the case where the user grants the permission. See the documentation
                    // for ActivityCompat#requestPermissions for more details.
                    return;
                }

                //Speech implementation
                mMap.setMyLocationEnabled(false);
                */


            if (getActivity() != null) {
                if(isAlertShown==false) {
                    String data1=" Your Destination Reached ";
                    int speechStatus1 = textToSpeech.speak(data1, TextToSpeech.QUEUE_FLUSH, null);
                    if (speechStatus1 == TextToSpeech.ERROR) {
                        Log.e("TTS", "Error in converting Text to Speech!");
                    }
                    sendData(MapEvents.ALERTVALUE_4, MapEvents.ALERTTYPE_4);

                        /*
                        AlertDialog.Builder builder = new AlertDialog.Builder(getContext(), R.style.yourDialog);
                        builder.setTitle("Alert");
                        builder.setIcon(R.drawable.car_icon_32);
                        builder.setMessage("Destination Reached")
                                .setCancelable(false)
                                .setPositiveButton(" Finish ", new DialogInterface.OnClickListener() {
                                    public void onClick(DialogInterface dialog, int id) {

                                        getActivity().onBackPressed();
                                    }
                                });
                        AlertDialog alert = builder.create();
                        alert.show();
                         */
                    isAlertShown=true;
                }else{

                }
            }
        }
    }

    public void CaluculateETAInRouteDeviationDirection( final double TotalDistance, final LatLng sourcePosition, final LatLng currentGpsPosition, LatLng DestinationPosition){
        // Log.e("Total Distance"," Route Deviation  ETA sourcePosition "+ sourcePosition);
        // Log.e("Total Distance"," Route Deviation  ETA  DestinationPosition "+ DestinationPosition);
        // Log.e("Total Distance"," Route Deviation  ETA  currentGpsPosition "+ currentGpsPosition);


        // Log.e("Total Distance","Total Distance"+ TotalRouteDeviatedDistanceInMTS);
        double  TotalDistanceDeviated= TotalRouteDeviatedDistanceInMTS*100000;

        // Log.e("Total Distance","Total Distance"+ TotalDistanceDeviated);

        ETACalclator etaCalculator1=new ETACalclator();
        double resultTotalETA=etaCalculator1.cal_time(TotalDistanceDeviated, maxSpeed);
        final double resultTotalTimeConverted = DecimalUtils.round(resultTotalETA,0);
        //  Log.e("resultTotalTime ","resultTotalTimeConverted ------- "+ resultTotalTimeConverted);

        double resultTravelledTimeConverted=0.0;
        // double resultNeedToTeavelTimeConverted=0.0;
        double resultNeedToTeavelTime=0.0;
        double EtaCrossedTime = 0.0;
        double EtaElapsed = 0.0;
        String etaCrossedFlag = "NO";

        double travelledDistance = showDistance(sourcePosition, currentGpsPosition);
        String travelledDistanceInMTS = String.format("%.0f", travelledDistance);
        ETACalclator etaCalculator = new ETACalclator();
        double resultTravelledTime = etaCalculator.cal_time(travelledDistance, 10);
        resultTravelledTimeConverted = DecimalUtils.round(resultTravelledTime, 0);


        double needToTravelDistance = TotalDistanceDeviated - travelledDistance;
        String needToTravelDistanceInMTS = String.format("%.0f", needToTravelDistance);
        ETACalclator etaCalculator2 = new ETACalclator();
        resultNeedToTeavelTime = etaCalculator2.cal_time(needToTravelDistance, 10);
        resultNeedToTeavelTimeConverted = DecimalUtils.round(resultNeedToTeavelTime, 0);

        // Log.e("TAG", " currentGpsPosition @@@@ " + currentGpsPosition);
        // Log.e("TAG", " travelledDistanceInMTS " + travelledDistanceInMTS);
        // Log.e("TAG", " travelled Time  " + resultTravelledTime);
        // Log.e("TAG", "  Need To travel DistanceInMTS " + needToTravelDistanceInMTS);
        // Log.e("TAG", "  Need To travel  Time " + resultNeedToTeavelTime);
        // double presentETATime = resultTravelledTime+resultNeedToTeavelTime;
        //tv2.setText("Time ETA : "+ resultNeedToTeavelTimeConverted +" SEC ");

        if (resultTravelledTimeConverted > resultTotalTimeConverted) {
            etaCrossedFlag = "YES";
            EtaCrossedTime = resultTravelledTime - resultTotalTimeConverted;
            EtaElapsed = DecimalUtils.round(EtaCrossedTime, 0);
        } else {
            etaCrossedFlag = "NO";
        }


        time.append("Distance").append(TotalDistance +" Meters ").append("\n").append("Total ETA ").append(resultTotalETA +" SEC ").append("\n").append(" Distance To Travel").append(resultNeedToTeavelTime +"Sec").append("Elapsed Time").append(EtaElapsed).append("\n");
        sendData(time.toString(),MapEvents.ALERTTYPE_2);

        // tv.setText("Total Time: "+ resultTotalTimeConverted +" SEC" );
        //  tv1.setText("Time  Traveled: "+ resultTravelledTimeConverted +" SEC ");

        // tv3.setText(" ETA Crossed Alert : "+ etaCrossedFlag + "  ");
    }
    public void TextImplementationRouteDeviationDirectionText(String directionTextInDeviation,String stPoint,String endPoint){
        // Log.e("TAG", "  START POSITION " + stPoint);
        //  Log.e("TAG", " END POSITION " + endPoint);
        //  Log.e("TAG", " END POSITION " + directionTextInDeviation);
        String stPoint_data=stPoint.replace("[","");
        String stPoint_data1=stPoint_data.replace("]","");
        String[] st_point=stPoint_data1.split(",");
        double st_point_lat= Double.parseDouble(st_point[1]);
        double st_point_lnag= Double.parseDouble(st_point[0]);
        LatLng st_Point_vertex=new LatLng(st_point_lat,st_point_lnag);

        String endPoint_data=endPoint.replace("[","");
        String endPoint_data1=endPoint_data.replace("]","");
        String[] end_point=endPoint_data1.split(",");
        double end_point_lat= Double.parseDouble(end_point[1]);
        double end_point_lnag= Double.parseDouble(end_point[0]);
        LatLng end_Point_vertex=new LatLng(end_point_lat,end_point_lnag);
        double Distance_To_travelIn_Vertex=showDistance(currentGpsPosition,end_Point_vertex);
        String Distance_To_travelIn_Vertex_Convetred=String.format("%.0f", Distance_To_travelIn_Vertex);

        if(directionTextInDeviation.equals("-")){

        }else {
            String data = directionTextInDeviation + " " + Distance_To_travelIn_Vertex_Convetred + "Meters";
            //String data=" in "+ DitrectionDistance +" Meters "+ directionTextFinal;
            int speechStatus = textToSpeech.speak(data, TextToSpeech.QUEUE_FLUSH, null);
            if (speechStatus == TextToSpeech.ERROR) {
                //   Log.e("TTS", "Error in converting Text to Speech!");
            }
            if(getActivity()!=null) {
                // Toast.makeText(getActivity(), "" + directionTextInDeviation + " " + Distance_To_travelIn_Vertex_Convetred + "Meters", Toast.LENGTH_SHORT).show();
                LayoutInflater inflater1 = getActivity().getLayoutInflater();
                @SuppressLint("WrongViewCast") View layout = inflater1.inflate(R.layout.custom_toast, (ViewGroup) getActivity().findViewById(R.id.textView_toast));
                TextView text = (TextView) layout.findViewById(R.id.textView_toast);

                text.setText("" + directionTextInDeviation + " " + Distance_To_travelIn_Vertex_Convetred + "Meters");
                ImageView image = (ImageView) layout.findViewById(R.id.image_toast);
                if (directionTextInDeviation.contains("Take Right")) {
                    image.setImageResource(R.drawable.direction_right);
                } else if (directionTextInDeviation.contains("Take Left")) {
                    image.setImageResource(R.drawable.direction_left);
                }
                new Handler(Looper.getMainLooper()).post(new Runnable() {
                    @Override
                    public void run() {
                        Toast toast = new Toast(getActivity().getApplicationContext());
                        toast.setDuration(Toast.LENGTH_LONG);
                        toast.setGravity(Gravity.TOP | Gravity.CENTER_HORIZONTAL, 0, 0);
                        toast.setGravity(Gravity.TOP, 0, 130);
                        toast.setView(layout);
                        toast.show();
                    }
                });

            }

        }

    }
    private void sendData(String comm,int AlertType) {
        //comm=time.toString();
        if(comm!=null) {
            Log.e("SendData", "SendData ------- " + comm + "AlertType" + AlertType);
            Callback.communicate(comm, AlertType);
        }else{

        }

    }
    private interface LatLngInterpolator {
        LatLng interpolate(float fraction, LatLng a, LatLng b);

        class LinearFixed implements LatLngInterpolator {
            @Override
            public LatLng interpolate(float fraction, LatLng a, LatLng b) {
                double lat = (b.latitude - a.latitude) * fraction + a.latitude;
                double lngDelta = b.longitude - a.longitude;
                // Take the shortest path across the 180th meridian.
                if (Math.abs(lngDelta) > 180) {
                    lngDelta -= Math.signum(lngDelta) * 360;
                }
                double lng = lngDelta * fraction + a.longitude;
                return new LatLng(lat, lng);
            }
        }
    }
    private static float computeRotation(float fraction, float start, float end) {
        float normalizeEnd = end - start; // rotate start to 0
        float normalizedEndAbs = (normalizeEnd + 360) % 360;

        float direction = (normalizedEndAbs > 180) ? -1 : 1; // -1 = anticlockwise, 1 = clockwise
        float rotation;
        if (direction > 0) {
            rotation = normalizedEndAbs;
        } else {
            rotation = normalizedEndAbs - 360;
        }

        float result = fraction * rotation + start;
        return (result + 360) % 360;
    }



    private  List<EdgeDataT> getAllEdgesData() {
        String query = "SELECT * FROM " + EdgeDataT.TABLE_NAME;
        Cursor c1 = sqlHandler.selectQuery(query);
        edgeDataList = (List<EdgeDataT>) SqlHandler.getDataRows(EdgeDataT.MAPPING, EdgeDataT.class, c1);
        sqlHandler.closeDataBaseConnection();
        return edgeDataList;
    }
    private List<LatLng> removeDuplicates(List<LatLng> EdgeWithoutDuplicates)
    {
        int count = edgeDataPointsList.size();

        for (int i = 0; i < count; i++)
        {
            for (int j = i + 1; j < count; j++)
            {
                if (edgeDataPointsList.get(i).equals(edgeDataPointsList.get(j)))
                {
                    edgeDataPointsList.remove(j--);
                    count--;
                }
            }
        }
        return EdgeWithoutDuplicates;
    }
    public static double distFrom(double lat1, double lng1, double lat2, double lng2) {
        double earthRadius = 6371000; //meters
        double dLat = Math.toRadians(lat2-lat1);
        double dLng = Math.toRadians(lng2-lng1);
        double a = sin(dLat/2) * sin(dLat/2) +
                cos(Math.toRadians(lat1)) * cos(Math.toRadians(lat2)) *
                        sin(dLng/2) * sin(dLng/2);
        double c = 2 * atan2(Math.sqrt(a), Math.sqrt(1-a));
        double dist = (float) (earthRadius * c);
        return dist;
    }
    public Set<Object> getKeysFromValue(Map<String, String> map, String key) {
        Set<Object> keys = new HashSet<Object>();
        for (Map.Entry<String, String> entry : map.entrySet()) {
            //if value != null
            if (entry.getKey().equals(key)){
                keys.add(entry.getValue());
            }
        }
        return keys;
    }

    public void getValidRouteData(){
        if (edgeDataList != null && edgeDataList.size() > 0) {
            edgeDataPointsList = new ArrayList<LatLng>();
            AllPointsList=new ArrayList();
            AllPointEdgeNo=new HashMap<>();
            AllPointEdgeDistaces=new HashMap<>();
            EdgeContainsDataList=new ArrayList<EdgeDataT>();
            for (int i = 0; i < edgeDataList.size(); i++) {
                EdgeDataT edge = new EdgeDataT(); //creating object for EDGETABLE
                edge = edgeDataList.get(i);
                int edgeNo = edge.getEdgeNo(); //Edge Number
                String stPoint = edge.getStartPoint(); //Start Point
                String endPoint = edge.getEndPoint();//End Point
                String points = edge.getAllPoints(); // All points in the edge
                String geometryText=edge.getGeometryText();
                String distanceInEdge = edge.getDistanceInVertex();
                TotalDistance =edge.getTotaldistance();
                if(points!=null){
                    String AllPoints = points.replace("[", "");
                    AllPoints = AllPoints.replace("]", "");
                    String[] AllPointsArray = AllPoints.split(", ");
                    for (int ap = 0; ap < AllPointsArray.length; ap++) {

                        String data = String.valueOf(AllPointsArray[ap]);
                        String dataStr = data.replace("[", "");
                        dataStr = dataStr.replace("]", "");
                        String ptData[] = dataStr.split(",");
                        double Lat = Double.parseDouble(ptData[0]);
                        double Lang = Double.parseDouble(ptData[1]);
                        PointData = new LatLng(Lat, Lang);
                        AllPointEdgeNo.put(String.valueOf(PointData),geometryText);
                        AllPointEdgeDistaces.put(String.valueOf(PointData),distanceInEdge);
                        AllPointsList.add(AllPointsArray[ap]);
                        PointData = new LatLng(Lang,Lat);
                        EdgeDataT edgePointData = new EdgeDataT(stPoint,endPoint,String.valueOf(PointData),geometryText,distanceInEdge);
                        EdgeContainsDataList.add(edgePointData);

                    }
                }

                for (int pntCount = 0; pntCount < AllPointsList.size(); pntCount++) {
                    String data = String.valueOf(AllPointsList.get(pntCount));
                    String dataStr = data.replace("[", "");
                    dataStr = dataStr.replace("]", "");
                    String ptData[] = dataStr.split(",");
                    double Lat = Double.parseDouble(ptData[0]);
                    double Lang = Double.parseDouble(ptData[1]);
                    PointData = new LatLng(Lat, Lang);
                    edgeDataPointsList.add(PointData);
                }

            }

            for(int k=0;k<EdgeContainsDataList.size();k++){
                EdgeDataT edgeK=EdgeContainsDataList.get(k);
                StringBuilder sb=new StringBuilder();
                sb.append("STPOINT :"+edgeK.getStartPoint()+"EndPt:"+edgeK.getEndPoint()+"Points:"+edgeK.getPositionMarkingPoint()+"Geometry TEXT:"+ edgeK.getGeometryText());
            }

        }
        //Getting Positions of Source and destinations
        LatLng sr_data=edgeDataPointsList.get(0);
        double x_sr=sr_data.latitude;
        double y_sr=sr_data.longitude;
        SourceNode= new LatLng(y_sr,x_sr);
        Log.e("SourceNode","SourceNode"+SourceNode);

        LatLng de_data=edgeDataPointsList.get(edgeDataPointsList.size()-1);
        double x_de=de_data.latitude;
        double y_de=de_data.longitude;
        DestinationNode=new LatLng(y_de,x_de);
        Log.e("DestinationNode","DestinationNode"+DestinationNode);

    }

    private LatLng findNearestPoint(final LatLng p, final LatLng start, final LatLng end) {
        if (start.equals(end)) {
            return start;
        }
        final double s0lat = Math.toRadians(p.latitude);
        final double s0lng = Math.toRadians(p.longitude);
        final double s1lat = Math.toRadians(start.latitude);
        final double s1lng = Math.toRadians(start.longitude);
        final double s2lat = Math.toRadians(end.latitude);
        final double s2lng = Math.toRadians(end.longitude);

        double s2s1lat = s2lat - s1lat;
        double s2s1lng = s2lng - s1lng;
        final double u = ((s0lat - s1lat) * s2s1lat + (s0lng - s1lng) * s2s1lng)
                / (s2s1lat * s2s1lat + s2s1lng * s2s1lng);
        if (u <= 0) {
            return start;
        }
        if (u >= 1) {
            return end;
        }

        return new LatLng(start.latitude + (u * (end.latitude - start.latitude)),
                start.longitude + (u * (end.longitude - start.longitude)));
    }

    public void addMarkers(){
        if(SourceNode!=null && DestinationNode!=null) {
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
               /*
                CameraPosition googlePlex1 = CameraPosition.builder()
                        .target(DestinationNode)
                        .zoom(18)
                        .tilt(45)
                        .build();

                mMap.animateCamera(CameraUpdateFactory.newCameraPosition(googlePlex1), 1000, null);

                */
        }else{
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
    public void GetRouteFromDBPlotOnMap(String FeatureResponse){
        String delQuery = "DELETE  FROM " + EdgeDataT.TABLE_NAME;
        sqlHandler.executeQuery(delQuery);
        JSONObject jsonObject = null;
        try {
            if(FeatureResponse!=null){
                jsonObject = new JSONObject(FeatureResponse);
                String ID = String.valueOf(jsonObject.get("$id"));
                String Status = jsonObject.getString("Status");
                double TotalDistance = jsonObject.getDouble("TotalDistance");
                TotalDistanceInMTS= TotalDistance*100000;
                JSONArray jSonRoutes = new JSONArray(jsonObject.getString("Route"));
                PolylineOptions polylineOptions = new PolylineOptions();
                Polyline polyline = null;
                convertedPoints=new ArrayList<LatLng>();
                for (int i = 0; i < jSonRoutes.length(); i++) {
                    points=new ArrayList();
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


                    String  stPoint=String.valueOf(jSonLegs.get(0));
                    String  endPoint=String.valueOf(jSonLegs.get(jSonLegs.length()-1));

                    stPoint=stPoint.replace("[","");
                    stPoint=stPoint.replace("]","");
                    String [] firstPoint=stPoint.split(",");
                    Double stPointLat= Double.valueOf(firstPoint[0]);
                    Double stPointLongi= Double.valueOf(firstPoint[1]);
                    LatLng stVertex=new LatLng(stPointLongi,stPointLat);

                    endPoint=endPoint.replace("[","");
                    endPoint=endPoint.replace("]","");
                    String [] secondPoint=endPoint.split(",");
                    Double endPointLat= Double.valueOf(secondPoint[0]);
                    Double endPointLongi= Double.valueOf(secondPoint[1]);
                    LatLng endVertex=new LatLng(endPointLongi,endPointLat);


                    double distance=showDistance(stVertex,endVertex);
                    String distanceInKM = String.valueOf(distance/1000);
                    StringBuilder query = new StringBuilder("INSERT INTO ");
                    query.append(EdgeDataT.TABLE_NAME).append("(edgeNo,distanceInVertex,startPoint,allPoints,geometryText,endPoint) values (")
                            .append("'").append(EdgeNo).append("',")
                            .append("'").append(distanceInKM).append("',")
                            // .append("'").append(String.valueOf(TotalDistanceInMTS)).append("',")
                            .append("'").append(jSonLegs.get(0)).append("',")
                            .append("'").append(points).append("',")
                            .append("'").append(GeometryText).append("',")
                            .append("'").append(jSonLegs.get(jSonLegs.length()-1)).append("')");
                    sqlHandler.executeQuery(query.toString());
                    sqlHandler.closeDataBaseConnection();
                    for (int p = 0; p < points.size(); p++) {
                        String listItem = points.get(p).toString();
                        listItem = listItem.replace("[", "");
                        listItem = listItem.replace("]", "");
                        String[] subListItem = listItem.split(",");
                        Double y = Double.valueOf(subListItem[0]);
                        Double x = Double.valueOf(subListItem[1]);
                        StringBuilder sb=new StringBuilder();
                        LatLng latLng = new LatLng(x, y);
                        convertedPoints.add(latLng);
                    }
                    Log.e("convertedPoints", " convertedPoints------ " +  convertedPoints.size());

                    // 55.065312867000046, 24.977084458000036
                    MarkerOptions markerOptions = new MarkerOptions();
                    for (int k = 0; k < convertedPoints.size(); k++) {
                        if(polylineOptions!=null && mMap!=null) {
                            markerOptions.position(convertedPoints.get(k));
                            markerOptions.title("Position");
                        }
                    }
                }
                polylineOptions.addAll(convertedPoints);
                polyline = mMap.addPolyline(polylineOptions);
                polylineOptions.color(Color.CYAN).width(30);
                mMap.addPolyline(polylineOptions);
                // polyline.setJointType(JointType.ROUND);
            }
        } catch (JSONException e) {
            e.printStackTrace();
        }

    }



    private BitmapDescriptor bitmapDescriptorFromVector(Context context, int vectorResId) {
        Drawable vectorDrawable = ContextCompat.getDrawable(context, vectorResId);
        vectorDrawable.setBounds(10, 0, vectorDrawable.getIntrinsicWidth(), vectorDrawable.getIntrinsicHeight());
        Bitmap bitmap = Bitmap.createBitmap(vectorDrawable.getIntrinsicWidth(), vectorDrawable.getIntrinsicHeight(), Bitmap.Config.ARGB_8888);
        Canvas canvas = new Canvas(bitmap);
        vectorDrawable.draw(canvas);
        return BitmapDescriptorFactory.fromBitmap(bitmap);
    }
    private double showDistance(LatLng latlng1, LatLng latLng2) {
        double distance = SphericalUtil.computeDistanceBetween(latlng1,latLng2);
        return distance;
    }

    @RequiresApi(api = Build.VERSION_CODES.KITKAT)
    List resultList=new ArrayList();
    public void InsertAllRouteData(String stNode,String destNode,String routeData){

        StringBuilder query = new StringBuilder("INSERT INTO ");
        query.append(RouteT.TABLE_NAME).append("(startNode,endNode,routeData) values (")
                .append("'").append(stNode).append("',")
                .append("'").append(destNode).append("',")
                .append("'").append(routeData).append("')");
        Log.e("query"," INSERTION query--"+ query);
        sqlHandler.executeQuery(query.toString());
        sqlHandler.closeDataBaseConnection();
    }


    private boolean checkPermission() {
        int result = ContextCompat.checkSelfPermission(getContext(), ACCESS_FINE_LOCATION);
        int result1 = ContextCompat.checkSelfPermission(getContext(), READ_EXTERNAL_STORAGE);

        return true;
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
            }break;
            case 1000: {
                // If request is cancelled, the result arrays are empty.
                if (grantResults.length > 0
                        && grantResults[0] == PackageManager.PERMISSION_GRANTED) {

                    if (isContinue) {
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
                    }
                } else {
                    Toast.makeText(getContext(), "Permission denied", Toast.LENGTH_SHORT).show();
                }
                break;
            }
        }
    }
        /*

        @SuppressLint("MissingPermission")
        @Override
        public void onRequestPermissionsResult(int requestCode, @NonNull String[] permissions, @NonNull int[] grantResults) {
            super.onRequestPermissionsResult(requestCode, permissions, grantResults);
            switch (requestCode) {
                case 1000: {
                    // If request is cancelled, the result arrays are empty.
                    if (grantResults.length > 0
                            && grantResults[0] == PackageManager.PERMISSION_GRANTED) {

                        if (isContinue) {
                            mFusedLocationClient.requestLocationUpdates(locationRequest, locationCallback, null);
                        } else {
                            mFusedLocationClient.getLastLocation().addOnSuccessListener(getActivity(), new OnSuccessListener<Location>() {
                                @Override
                                public void onSuccess(Location location) {
                                    if (location != null) {
                                        wayLatitude = location.getLatitude();
                                        wayLongitude = location.getLongitude();
                                        Log.v("APP DATA","LAT VALUE"+wayLatitude);
                                        Log.v("APP DATA","LAT VALUE"+wayLongitude);
                                        txtLocation.setText(String.format(Locale.US, "%s - %s", wayLatitude, wayLongitude));


                                    } else {
                                        mFusedLocationClient.requestLocationUpdates(locationRequest, locationCallback, null);
                                    }
                                }
                            });
                        }
                    } else {
                        Toast.makeText(getContext(), "Permission denied", Toast.LENGTH_SHORT).show();
                    }
                    break;
                }
            }
        }
        */

    private LatLng getLocation() {
            /*
            if (ActivityCompat.checkSelfPermission(getContext(),
            android.Manifest.permission.ACCESS_FINE_LOCATION) != PackageManager.PERMISSION_GRANTED &&
            ActivityCompat.checkSelfPermission(getContext(),
                    android.Manifest.permission.ACCESS_COARSE_LOCATION) != PackageManager.PERMISSION_GRANTED) {
         requestPermissions(getActivity(),
                new String[]{android.Manifest.permission.ACCESS_COARSE_LOCATION,
                        android.Manifest.permission.ACCESS_FINE_LOCATION},
                REQUEST_LOCATION);

             */

        // } else {
        if (isContinue) {
            // Log.v("APP DATA","checking IF ic continue "+isContinue);
            if( mFusedLocationClient!=null && locationRequest!=null && locationCallback!=null) {
                mFusedLocationClient.requestLocationUpdates(locationRequest, locationCallback, null);
            }
            // Log.v("APP DATA","checking IF ");


        } else {
            mFusedLocationClient.getLastLocation().addOnSuccessListener(getActivity(), new OnSuccessListener<Location>() {
                @Override
                public void onSuccess(Location location) {
                    //  Log.v("APP DATA","LOCATION NULL");
                    //   Log.v("APP DATA","checking else ic continue "+isContinue);
                    if (location != null) {
                        wayLatitude = location.getLatitude();
                        wayLongitude = location.getLongitude();
                        //just for trail
                        String S= String.valueOf(location.getLatitude());
                        // Log.v("APP DATA",""+S);
                        // Log.e("latitude FROM SERVICE",location.getLatitude()+"");
                        //  Log.e("longitude FROM SERVICE",location.getLongitude()+"");
                        //txtLocation.setText(String.format(Locale.US, "%s - %s", wayLatitude, wayLongitude));

                        Log.d("TAG", "location DATA ........"+"CURRENT GPS POSITION : "+ wayLatitude+","+wayLongitude  );
                    } else {
                        mFusedLocationClient.requestLocationUpdates(locationRequest, locationCallback, null);
                    }
                }
            });
        }
        //  }
        return currentGPSPosition;
    }
    @Override
    public void onActivityResult(int requestCode, int resultCode, Intent data) {
        super.onActivityResult(requestCode, resultCode, data);
        if (resultCode == Activity.RESULT_OK) {
            if (requestCode == AppConstants.GPS_REQUEST) {
                isGPS = true; // flag maintain before get location
            }
        }
    }
    private void animateCarMove(final Marker marker, final LatLng beginLatLng, final LatLng endLatLng, final long duration) {
        final Handler handler = new Handler();
        final long startTime = SystemClock.uptimeMillis();
        final Interpolator interpolator = new LinearInterpolator();
        // set car bearing for current part of path
        float angleDeg = (float)(180 * getAngle(beginLatLng, endLatLng) / Math.PI);
        Matrix matrix = new Matrix();
        matrix.postRotate(angleDeg);
        // marker.setIcon(BitmapDescriptorFactory.fromBitmap(Bitmap.createBitmap(mMarkerIcon, 0, 0,mMarkerIcon.getWidth(), mMarkerIcon.getHeight(), matrix, true)));
        //marker.setIcon(BitmapDescriptorFactory.fromBitmap(Bitmap.createBitmap(mMarkerIcon, 0, 0, centerX,centerY, matrix, true)));
        handler.post(new Runnable() {
            @RequiresApi(api = Build.VERSION_CODES.JELLY_BEAN)
            @Override
            public void run() {
                // calculate phase of animation
                long elapsed = SystemClock.uptimeMillis() - startTime;
                float t = interpolator.getInterpolation((float) elapsed / duration);
                // calculate new position for marker
                double lat = (endLatLng.latitude - beginLatLng.latitude) * t + beginLatLng.latitude;
                double lngDelta = endLatLng.longitude - beginLatLng.longitude;
                if (Math.abs(lngDelta) > 180) {
                    lngDelta -= Math.signum(lngDelta) * 360;
                }
                Location location= new Location(LocationManager.GPS_PROVIDER);
                location.setLatitude(endLatLng.latitude);
                location.setLongitude(endLatLng.longitude);
                float bearingMap= location.getBearing();
                //  float bearingMap= mMap.getCameraPosition().bearing;
                float bearing = (float) bearingBetweenLocations(beginLatLng,endLatLng);
                float angle = -azimuthInDegress+bearing;
                float rotation = -azimuthInDegress * 360 / (2 * 3.14159f) ;
                double lng = lngDelta * t + beginLatLng.longitude;
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
                if (t < 1.0) {
                    handler.postDelayed(this, 16);
                } else {
                    float beginAngle = (float)(90 * getAngle(beginLatLng, endLatLng) / Math.PI);
                    float endAngle = (float)(90 * getAngle(currentGpsPosition, endLatLng) / Math.PI);
                    computeRotation(10,beginAngle,endAngle);
                }
            }
        });
    }
    private void animateCarMoveNotUpdateMarker(final Marker marker, final LatLng beginLatLng, final LatLng endLatLng, final long duration) {
        final Handler handler = new Handler();
        final long startTime = SystemClock.uptimeMillis();
        final Interpolator interpolator = new LinearInterpolator();
        // set car bearing for current part of path
        float angleDeg = (float)(180 * getAngle(beginLatLng, endLatLng) / Math.PI);
        Matrix matrix = new Matrix();
        matrix.postRotate(angleDeg);
        // marker.setIcon(BitmapDescriptorFactory.fromBitmap(Bitmap.createBitmap(mMarkerIcon, 0, 0,mMarkerIcon.getWidth(), mMarkerIcon.getHeight(), matrix, true)));
        //marker.setIcon(BitmapDescriptorFactory.fromBitmap(Bitmap.createBitmap(mMarkerIcon, 0, 0, centerX,centerY, matrix, true)));
        handler.post(new Runnable() {
            @RequiresApi(api = Build.VERSION_CODES.JELLY_BEAN)
            @Override
            public void run() {
                // calculate phase of animation
                long elapsed = SystemClock.uptimeMillis() - startTime;
                float t = interpolator.getInterpolation((float) elapsed / duration);
                // calculate new position for marker
                double lat = (endLatLng.latitude - beginLatLng.latitude) * t + beginLatLng.latitude;
                double lngDelta = endLatLng.longitude - beginLatLng.longitude;
                if (Math.abs(lngDelta) > 180) {
                    lngDelta -= Math.signum(lngDelta) * 360;
                }
                Location location= new Location(LocationManager.GPS_PROVIDER);
                location.setLatitude(endLatLng.latitude);
                location.setLongitude(endLatLng.longitude);
                float bearingMap= location.getBearing();
                //  float bearingMap= mMap.getCameraPosition().bearing;
                float bearing = (float) bearingBetweenLocations(beginLatLng,endLatLng);
                float angle = -azimuthInDegress+bearing;
                float rotation = -azimuthInDegress * 360 / (2 * 3.14159f) ;
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
                    handler.postDelayed(this, 16);
                } else {
                    float beginAngle = (float)(90 * getAngle(beginLatLng, endLatLng) / Math.PI);
                    float endAngle = (float)(90 * getAngle(currentGpsPosition, endLatLng) / Math.PI);
                    computeRotation(10,beginAngle,endAngle);
                }
            }
        });
    }

    private double bearingBetweenLocations(LatLng latLng1, LatLng latLng2) {
        double PI = 3.14159;
        double lat1 = latLng1.latitude * PI / 180;
        double long1 = latLng1.longitude * PI / 180;
        double lat2 = latLng2.latitude * PI / 180;
        double long2 = latLng2.longitude * PI / 180;
        double dLon = (long2 - long1);
        double y = sin(dLon) * cos(lat2);
        double x = cos(lat1) * sin(lat2) - sin(lat1)
                * cos(lat2) * cos(dLon);
        double brng = atan2(y, x);
        brng = Math.toDegrees(brng);
        brng = (brng + 360) % 360;
        return brng;
    }

    private static double getAngle(LatLng beginLatLng, LatLng endLatLng) {
        double f1 = Math.PI * beginLatLng.latitude / 180;
        double f2 = Math.PI * endLatLng.latitude / 180;
        double dl = Math.PI * (endLatLng.longitude - beginLatLng.longitude) / 180;
        return atan2(sin(dl) * cos(f2) , cos(f1) * sin(f2) - sin(f1) * cos(f2) * cos(dl));
    }

    @RequiresApi(api = Build.VERSION_CODES.JELLY_BEAN)
    public void MoveWithGpsPointInBetWeenAllPoints(final LatLng PrevousGpsPosition ,final LatLng currentGpsPosition){

        LatLng OldGps = null,nayaGps;
        List<LatLng> EdgeWithoutDuplicates = removeDuplicates(edgeDataPointsList);
        nearestValuesMap=new HashMap<>();
        if (EdgeWithoutDuplicates != null && EdgeWithoutDuplicates.size() > 0) {
            String FirstCordinate="",SecondCordinate="";
            List distancesList = new ArrayList();
            distanceValuesList = new ArrayList();
            HashMap<String,String> hash_map = new HashMap<String, String>();
            for (int epList = 0; epList < EdgeWithoutDuplicates.size(); epList++) {
                LatLng PositionMarkingPoint = EdgeWithoutDuplicates.get(epList);
                // Log.e("Distances List","Distances List PositionMarkingPoint"+PositionMarkingPoint);
                // Log.e("Distances List","Distances List currentGpsPosition "+currentGpsPosition);
                double distance = distFrom(PositionMarkingPoint.latitude,PositionMarkingPoint.longitude,currentGpsPosition.longitude,currentGpsPosition.latitude);
                hash_map.put(String.valueOf(distance), String.valueOf(EdgeWithoutDuplicates.get(epList)));
                distancesList.add(distance);
                Collections.sort(distancesList);
            }
            for(int i=0;i<distancesList.size();i++) {
                // Log.e("Distances List","Distances List"+distancesList.get(i));
            }

            String FirstShortestDistance = String.valueOf(distancesList.get(0));
            String SecondShortestDistance = String.valueOf(distancesList.get(1));
            boolean answerFirst= hash_map.containsKey(FirstShortestDistance);
            if (answerFirst) {
                System.out.println("The list contains " + FirstShortestDistance);
                FirstCordinate = (String)hash_map.get(FirstShortestDistance);
                key= String.valueOf(getKeysFromValue(AllPointEdgeNo,FirstCordinate));
                distanceKey= String.valueOf(getKeysFromValue(AllPointEdgeDistaces,FirstCordinate));
            } else {
                System.out.println("The list does not contains "+ "FALSE");
            }
            boolean answerSecond= hash_map.containsKey(SecondShortestDistance);
            if (answerSecond) {
                System.out.println("The list contains " + SecondShortestDistance);
                SecondCordinate = (String)hash_map.get(SecondShortestDistance);

            } else {
                System.out.println("The list does not contains "+ "FALSE");
            }
            String First= FirstCordinate.replace("lat/lng: (","");
            First= First.replace(")","");
            String[] FirstLatLngsData=First.split(",");
            double FirstLatitude= Double.valueOf(FirstLatLngsData[0]);
            double FirstLongitude= Double.valueOf(FirstLatLngsData[1]);

            geometryDirectionText=key;
            geometryDirectionDistance=distanceKey;

            String Second= SecondCordinate.replace("lat/lng: (","");
            Second= Second.replace(")","");
            String[] SecondLatLngsData=Second.split(",");
            double SecondLatitude= Double.valueOf(SecondLatLngsData[0]);
            double SecondLongitude= Double.valueOf(SecondLatLngsData[1]);

            double x= currentGpsPosition.longitude;
            double y= currentGpsPosition.longitude;
            int value = (int)x;
            int value1 = (int)y;
            LatLng source=new LatLng(FirstLongitude,FirstLatitude);
            LatLng destination=new LatLng(SecondLongitude,SecondLatitude);
            NavigationDirection(currentGpsPosition, DestinationNode);

            if(nearestPositionPoint != null) {
                OldGps = nearestPositionPoint;
            }

            nearestPositionPoint= findNearestPoint(currentGpsPosition,source,destination);
            Log.e("nearestPositionPoint","nearestPositionPoint"+nearestPositionPoint);
            OldNearestGpsList.add(nearestPositionPoint);

        }
        Log.e("nearestPositionPoint","nearestPositionPoint LIST "+ OldNearestGpsList.toString());

/*
      //  Log.e("EdgeSt Point", "End point" + OldNearestGpsList.size());
        if(OldNearestGpsList.isEmpty() && OldNearestGpsList.size()==0){
            OldGps=OldNearestGpsList.get(0);
            int indexVal=OldNearestGpsList.indexOf(nearestPositionPoint);
            nayaGps=OldNearestGpsList.get(indexVal);
        }else{
            //int indexVal=OldNearestGpsList.indexOf(nearestPositionPoint);
            OldGps=OldNearestGpsList.get(OldNearestGpsList.size() - 2);
            nayaGps= new LatLng(nearestPositionPoint.latitude, nearestPositionPoint.longitude);//OldNearestGpsList.get(indexVal);
        }
        */
        nearestValuesMap.put(String.valueOf(nearestPositionPoint),geometryDirectionText);
        nearestPointValuesList.add(nearestPositionPoint);
        //  if(currentGpsPosition.equals(LatLngDataArray.get(LatLngDataArray.size()-1))){
        //     nearestPointValuesList.add(DestinationPosition);
        // }
        float bearing=0;

        if(OldGps!=null && nearestPositionPoint!=null) {
            bearing = (float) bearingBetweenLocations(OldGps, nearestPositionPoint); //correct method to change orientation of map
            Log.e("nearestPositionPoint", "OldGps ----1" + OldGps);
            Log.e("nearestPositionPoint", "nearestPositionPoint ----1" + nearestPositionPoint);
            mPositionMarker = mMap.addMarker(new MarkerOptions()
                    .position(SourceNode)
                    .title("currentLocation")
                    .anchor(0.5f, 0.5f)
                    .rotation(bearing)
                    .flat(true));

            animateCarMove(mPositionMarker, OldGps, nearestPositionPoint, 10000);


        }

        caclulateETA(TotalDistanceInMTS,SourceNode,currentGpsPosition,DestinationNode);
       // verifyRouteDeviation(PrevousGpsPosition,currentGpsPosition,DestinationNode,40,EdgeWithoutDuplicates);
        AlertDestination(currentGpsPosition);

        int width =getView().getMeasuredWidth();
        Log.e("width","width"+width);
        int height =getView().getMeasuredHeight();
        Log.e("Height","Height"+height);
        //mMap.moveCamera(CameraUpdateFactory.newLatLngZoom(nearestPositionPoint, 18));


        Projection p = mMap.getProjection();
        Point bottomRightPoint = p.toScreenLocation(p.getVisibleRegion().nearRight);
        Point center = new Point(bottomRightPoint.x/2,bottomRightPoint.y/2);
        Point offset = new Point(center.x, (center.y+(height/4)));
        LatLng centerLoc = p.fromScreenLocation(center);
        LatLng offsetNewLoc = p.fromScreenLocation(offset);
        double offsetDistance = SphericalUtil.computeDistanceBetween(centerLoc, offsetNewLoc);
        LatLng shadowTgt = SphericalUtil.computeOffset(nearestPositionPoint,offsetDistance,bearing);

        CameraPosition currentPlace = new CameraPosition.Builder()
                .target(shadowTgt)
                .bearing(bearing).tilt(65.5f).zoom(20)
                .build();
        mMap.animateCamera(CameraUpdateFactory.newCameraPosition(currentPlace), 10000, null);
    }
    @Override
    public void onPause() {
        super.onPause();

    }
    public void writeLogFile(){
        if ( isExternalStorageWritable() ) {

            File appDirectory = new File( Environment.getExternalStorageDirectory() + "/RORO_AppLogs" );
            File logDirectory = new File( appDirectory + "/log" );
            File logFile = new File( logDirectory, "RORO_Log" + System.currentTimeMillis() + ".txt" );

            // create app folder
            if ( !appDirectory.exists() ) {
                appDirectory.mkdir();
            }

            // create log folder
            if ( !logDirectory.exists() ) {
                logDirectory.mkdir();
            }

            // clear the previous logcat and then write the new one to the file
            try {
                Process process = Runtime.getRuntime().exec("logcat -c");
                process = Runtime.getRuntime().exec("logcat -f " + logFile);
            } catch ( IOException e ) {
                e.printStackTrace();
            }

        } else if ( isExternalStorageReadable() ) {
            // only readable
        } else {
            // not accessible
        }
    }


    /* Checks if external storage is available for read and write */
    public boolean isExternalStorageWritable() {
        String state = Environment.getExternalStorageState();
        if ( Environment.MEDIA_MOUNTED.equals( state ) ) {
            return true;
        }
        return false;
    }

    /* Checks if external storage is available to at least read */
    public boolean isExternalStorageReadable() {
        String state = Environment.getExternalStorageState();
        if ( Environment.MEDIA_MOUNTED.equals( state ) ||
                Environment.MEDIA_MOUNTED_READ_ONLY.equals( state ) ) {
            return true;
        }
        return false;
    }

}
/*

                                 /*
                                 if(commonPoints.size()==0){
                                     Log.e("List Verification","List Verification  new_unCommonPoints -- DATA "+ "NEW ROUTE");
                                     Log.e("Route Deviation", " IS ROUTE VERIFY  ###### " + " Route NOT EQUAL");
                                     isRouteDeviated = true;
                                     LayoutInflater inflater1 = getActivity().getLayoutInflater();
                                     @SuppressLint("WrongViewCast") View layout = inflater1.inflate(R.layout.custom_toast, (ViewGroup) getActivity().findViewById(R.id.textView_toast));
                                     TextView text = (TextView) layout.findViewById(R.id.textView_toast);

                                     text.setText("Route Deviated");

                                     Toast toast = new Toast(getActivity().getApplicationContext());
                                     toast.setDuration(Toast.LENGTH_LONG);
                                     toast.setGravity(Gravity.TOP | Gravity.CENTER_HORIZONTAL, 0, 0);
                                     toast.setGravity(Gravity.TOP, 0, 150);
                                     toast.setView(layout);
                                     toast.show();
                                     StringBuilder routeDeviatedAlert = new StringBuilder();
                                     routeDeviatedAlert.append("ROUTE DEVIATED" + "RouteDeviatedSourcePosition : " + RouteDeviatedSourcePosition);
                                     sendData(MapEvents.ALERTVALUE_3, MapEvents.ALERTTYPE_3);
                                     if (mPositionMarker != null) {
                                         mPositionMarker.remove();
                                         Log.e("REMOVING MARKER", "REMOVING MARKER");
                                     }
                                     mPositionMarker = mMap.addMarker(new MarkerOptions()
                                             .position(currentGpsPosition)
                                             .title("currentLocation")
                                             .anchor(0.5f, 0.5f)
                                             .flat(true)
                                             .icon(bitmapDescriptorFromVector(getContext(), R.drawable.gps_transperent_98)));


                                     CameraUpdate center =
                                             CameraUpdateFactory.newLatLng(currentGpsPosition);
                                     CameraUpdate zoom = CameraUpdateFactory.zoomTo(22);
                                     mMap.moveCamera(center);
                                     mMap.animateCamera(zoom);
                                     if (mPositionMarker != null && mPositionMarker.isVisible() == true) {
                                         PolylineOptions polylineOptions = new PolylineOptions();
                                         // polylineOptions.add(OldGPSPosition);
                                         polylineOptions.addAll(RouteDeviationConvertedPoints);
                                         Polyline polyline = mMap.addPolyline(polylineOptions);
                                         polylineOptions.color(Color.RED).width(30);
                                         mMap.addPolyline(polylineOptions);
                                         polyline.setJointType(JointType.ROUND);
                                     }


                                 }else if(commonPoints.size()>0){
                                     Log.e("List Verification","List Verification  new_unCommonPoints -- DATA "+ "  Points Matched Plot on Route");
                                     Log.e("List Verification","List Verification  new_unCommonPoints -- DATA "+ "NEW ROUTE");
                                     Log.e("Route Deviation", " IS ROUTE VERIFY  ###### " + " Route NOT EQUAL");
                                     isRouteDeviated = true;
                                     LayoutInflater inflater1 = getActivity().getLayoutInflater();
                                     @SuppressLint("WrongViewCast") View layout = inflater1.inflate(R.layout.custom_toast, (ViewGroup) getActivity().findViewById(R.id.textView_toast));
                                     TextView text = (TextView) layout.findViewById(R.id.textView_toast);

                                     text.setText("Route Deviated");

                                     Toast toast = new Toast(getActivity().getApplicationContext());
                                     toast.setDuration(Toast.LENGTH_LONG);
                                     toast.setGravity(Gravity.TOP | Gravity.CENTER_HORIZONTAL, 0, 0);
                                     toast.setGravity(Gravity.TOP, 0, 150);
                                     toast.setView(layout);
                                     toast.show();
                                     StringBuilder routeDeviatedAlert = new StringBuilder();
                                     routeDeviatedAlert.append("ROUTE DEVIATED" + "RouteDeviatedSourcePosition : " + RouteDeviatedSourcePosition);
                                     sendData(MapEvents.ALERTVALUE_3, MapEvents.ALERTTYPE_3);
                                     if (mPositionMarker != null) {
                                         mPositionMarker.remove();
                                         Log.e("REMOVING MARKER", "REMOVING MARKER");
                                     }
                                     mPositionMarker = mMap.addMarker(new MarkerOptions()
                                             .position(currentGpsPosition)
                                             .title("currentLocation")
                                             .anchor(0.5f, 0.5f)
                                             .flat(true)
                                             .icon(bitmapDescriptorFromVector(getContext(), R.drawable.gps_transperent_98)));


                                     CameraUpdate center =
                                             CameraUpdateFactory.newLatLng(currentGpsPosition);
                                     CameraUpdate zoom = CameraUpdateFactory.zoomTo(22);
                                     mMap.moveCamera(center);
                                     mMap.animateCamera(zoom);
                                     if (mPositionMarker != null && mPositionMarker.isVisible() == true) {
                                         PolylineOptions polylineOptions = new PolylineOptions();
                                         // polylineOptions.add(OldGPSPosition);
                                         polylineOptions.addAll(new_unCommonPoints);
                                         Polyline polyline = mMap.addPolyline(polylineOptions);
                                         polylineOptions.color(Color.RED).width(30);
                                         mMap.addPolyline(polylineOptions);
                                         polyline.setJointType(JointType.ROUND);
                                     }

                                 }else if(new_unCommonPoints.size()==0){
                                     Log.e("List Verification","List Verification  new_unCommonPoints -- DATA "+ " OLD ROUTE");
                                     Log.e("Route Deviation", " IS ROUTE VERIFY  ###### " + " Route EQUAL");
                                     isRouteDeviated = false;

                                 }
                                 */

                                /*
                                 boolean isRourteVerify =  checkPointsOfExistingRoutewithNewRoute(EdgeWithoutDuplicates, RouteDeviationPointsForComparision);

                                 Log.e("Route Deviation", " IS ROUTE VERIFY  ###### " + isRourteVerify);

                                 if(isRourteVerify==true){
                                     Log.e("Route Deviation", " IS ROUTE VERIFY  ###### " + " Route EQUAL");
                                     isRouteDeviated = false;

                                 }else {
                                     Log.e("Route Deviation", " IS ROUTE VERIFY  ###### " + " Route NOT EQUAL");
                                     isRouteDeviated = true;
                                     LayoutInflater inflater1 = getActivity().getLayoutInflater();
                                     @SuppressLint("WrongViewCast") View layout = inflater1.inflate(R.layout.custom_toast, (ViewGroup) getActivity().findViewById(R.id.textView_toast));
                                     TextView text = (TextView) layout.findViewById(R.id.textView_toast);

                                     text.setText("Route Deviated");

                                     Toast toast = new Toast(getActivity().getApplicationContext());
                                     toast.setDuration(Toast.LENGTH_LONG);
                                     toast.setGravity(Gravity.TOP | Gravity.CENTER_HORIZONTAL, 0, 0);
                                     toast.setGravity(Gravity.TOP, 0, 150);
                                     toast.setView(layout);
                                     toast.show();
                                     StringBuilder routeDeviatedAlert = new StringBuilder();
                                     routeDeviatedAlert.append("ROUTE DEVIATED" + "RouteDeviatedSourcePosition : " + RouteDeviatedSourcePosition);
                                     sendData(MapEvents.ALERTVALUE_3, MapEvents.ALERTTYPE_3);
                                     if (mPositionMarker != null) {
                                         mPositionMarker.remove();
                                         Log.e("REMOVING MARKER", "REMOVING MARKER");
                                     }
                                     mPositionMarker = mMap.addMarker(new MarkerOptions()
                                             .position(currentGpsPosition)
                                             .title("currentLocation")
                                             .anchor(0.5f, 0.5f)
                                             .flat(true)
                                             .icon(bitmapDescriptorFromVector(getContext(), R.drawable.gps_transperent_98)));


                                     CameraUpdate center =
                                             CameraUpdateFactory.newLatLng(currentGpsPosition);
                                     CameraUpdate zoom = CameraUpdateFactory.zoomTo(22);
                                     mMap.moveCamera(center);
                                     mMap.animateCamera(zoom);
                                     if (mPositionMarker != null && mPositionMarker.isVisible() == true) {
                                         PolylineOptions polylineOptions = new PolylineOptions();
                                         // polylineOptions.add(OldGPSPosition);
                                         polylineOptions.addAll(RouteDeviationConvertedPoints);
                                         Polyline polyline = mMap.addPolyline(polylineOptions);
                                         polylineOptions.color(Color.RED).width(30);
                                         mMap.addPolyline(polylineOptions);
                                         polyline.setJointType(JointType.ROUND);
                                     }
                                 }

                                 */
