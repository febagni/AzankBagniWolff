// Signatures

sig Name, Password, Email, BankAccount {}
sig Location {}
sig BatteryType, BatteryStatus {}

sig SystemEMSP {
	connection: one SystemCPMS
}
sig SystemCPMS {
	connection: one SystemEMSP
}

abstract sig ChargingTypes {}
one sig SLOW extends ChargingTypes {}
one sig FAST extends ChargingTypes {}
one sig RAPID extends ChargingTypes {}

abstract sig Bool {}
one sig True, False extends Bool {}

abstract sig User {
    name: one Name,
    email: one Email,
    password: one Password,
    bankAccount: one BankAccount
}

sig CPO extends User {
    station: some ChargingStation,
    account: one CPMS
}

sig ChargingStation {
    location: one Location,
    freeSockets: one Int,
    energyBatteries: one Int,
    connectedCars: one Int,
    sockets: some ChargingSocket,
    owner: one CPO,
    batteries: set Battery,
    system: one SystemCPMS
} {
    freeSockets >= 0
    energyBatteries >= 0
    connectedCars >= 0
}

sig ChargingSocket {
    station: one ChargingStation,
    price: one Int, 
    isOccupied: one Bool,
    timeUntilFree: one Int,
    powerAlreadyAbsorbed: one Int,
    type: one ChargingTypes
} {
    price >= 0
    timeUntilFree >= 0
    powerAlreadyAbsorbed >= 0
}

sig DSO {
    energy: one Int,
    price: one Int
} {
    price >= 0
    energy >= 0
}

sig CPMS {
    dso: some DSO,
    system: one SystemCPMS
}

sig EMSP {
    system: one SystemEMSP
}

sig Battery {
    status: one BatteryStatus,
    type: one BatteryType
}

sig Car {
    battery: one Battery
}

sig CarOwner extends User {
    car: one Car,
    account: one EMSP
}

// PREDICATES AND FACTS

// unique emails for every user 
fact uniqueEmails {
	no disjoint u1 , u2 : User | u1.email = u2. email 
}

// all emails connected to a user
fact allEmailConnected {
	all e: Email | one u: User | e = u.email
}

// unique back account for every user 
fact uniqueBankAccounts {
	no disjoint u1 , u2 : User | u1.bankAccount = u2.bankAccount
}

// all bank accounts connected to a user
fact allBankAccountsConnected {
	all b: BankAccount | one u: User | b = u.bankAccount
}

// unique name for every user 
fact uniqueNames {
	no disjoint u1 , u2 : User | u1.name = u2.name
}

// all names connected to a user
fact allNamesConnected {
	all n: Name | one u: User | n = u.name
}

// all passwords connected to a user
fact allPasswordsConnected {
	all p: Password | some u: User | p = u.password //all all, because there can be equal passwords (verify)
}

//---

// unique CPMS account for every CPO
fact uniqueCpmsAccount {
	no disjoint c1 , c2 : CPO | c1.account = c2.account 
}

// all CPMS are connected to one CPO
fact allCPMSConnected {
	all c: CPMS | one u: CPO | c = u.account
}

// ---

// unique location for every charging station
fact uniqueChargingStationLocation {
	no disjoint c1, c2 : ChargingStation | c1.location = c2.location
}

// all Locations connected to a Charging Station 
fact allLocationsConnected {
	all l: Location | one c: ChargingStation | l = c.location
}

// ---

// unique set of charging stations for every CPO
fact uniqueChargingStationSetForCPO {
	no disjoint c1 , c2 : CPO | c1.station = c2.station
}

// all CPOs connected to charging stations
fact allCPOConnectedAllChargingStation{
	all c: CPO, s: ChargingStation | s in c.station iff s.owner = c
}

// ---

// all sockets connected one charging station
fact allSocketsConnectedOneChargingStation{
	all so: ChargingSocket, st: ChargingStation | so in st.sockets iff so.station = st
}

// unique set of charging sockets for every charging station
fact uniqueChargingSockets {
	no disjoint s1 , s2 : ChargingStation | s1.sockets = s2.sockets 
}

// ---

// all BatteryStatus connected to a Battery 
fact allBatteryStatusConnected {
	all s: BatteryStatus | one b: Battery | s = b.status
}

// all BatteryType connected to a Battery 
fact allBatteryTypeConnected {
	all t: BatteryType | one b: Battery | t = b.type
}

// -- 

// unique car battery for every car
fact uniqueCarBattery {
	no disjoint c1 , c2 : Car | c1.battery = c2.battery 
}

// unique car battery for every car and charging station
fact uniqueBatteryCarStation {
	no disjoint c: Car, s: ChargingStation | c.battery in s.batteries
}

// --

// unique car for every carowner 
fact uniqueCarCarOwner{
	no disjoint u1 , u2 : CarOwner | u1.car = u2.car 
}

// all Car are connected to one CarOwner
fact allCarCarOwnerConnected {
	all c: Car | one u: CarOwner | c = u.car
}


// unique EMSP account for every CarOwner
fact  {
	no disjoint c1 , c2 : CarOwner | c1.account = c2.account 
}

// all EMSP are connected to one CarOwner
fact allEMSPConnected {
	all e: EMSP | one u: CarOwner | e = u.account
}

// --

// all EMSP interfaces connected to system EMSP
fact allSystemEMSPConnected {
	all e: EMSP | one s: SystemEMSP | s = e.system
}

// all CPMS interfaces connected to system CPMS
fact allSystemCPMSConnected {
	all c: CPMS | one s: SystemCPMS | s = c.system
}

// all ChargingStations connected to system EMSP
fact allSystemCPMSChargingStationConnected {
	all c: ChargingStation | one s: SystemCPMS | s = c.system
}

// system EMSP connected with system CPMS
fact allSystemConnected {
	all s1: SystemCPMS, s2: SystemEMSP | s1 = s2.connection iff s1.connection = s2
}

// --

// Dynamic Modeling

// add DSO in a CPMS 
pred addDSO [cp,cpnew: CPMS, ds: DSO]{ 
	cpnew.dso = cp.dso + ds  
}

//add Socket in Station
pred addSocket [cs,csnew: ChargingStation, s: ChargingSocket]{
	csnew.sockets = cs.sockets + s
}

//add Battery in Station
pred addBattery [cs,csnew: ChargingStation, b: Battery]{
	csnew.batteries = cs.batteries + b
}

//add Station in CPO
pred addStation [cp,cpnew: CPO, cs: ChargingStation]{
	cpnew.station = cp.station + cs
}

// --

// Examples of possible assertions

assert NoCarWithSameBattery {
	no disjoint c1, c2: Car | c1.battery = c2.battery
}

assert NoSameBankAccountForUsers {
	no disjoint u1 , u2 : User | u1.bankAccount = u2.bankAccount
}	

//check NoCarWithSameBattery for 8
//check NoSameBankAccountForUsers for 8

// --

pred world1 {
	#CPO=1
	#ChargingStation=2
	#Battery=3
	#Car=1
	#ChargingSocket=3
}

pred world2 {
	#CPO=3
	#Car=1
	#EMSP=1
	#Battery=3
	#SystemEMSP=1
	#SystemCPMS=1
}

run world2 for 6
