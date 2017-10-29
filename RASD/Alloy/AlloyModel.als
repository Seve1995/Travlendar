//DATA TYPE SIGNATURES


open util/integer

sig Strings{}
sig TravelMeansType{}

abstract sig Boolean{}
one sig True extends Boolean{}
one sig False extends Boolean{}

sig Time{
	hour: one Int, 
	minute: one Int
}
{
	hour>=0 and hour<=23
	minute>=0 and minute<=59
}
sig PositiveFloat{
	leftPart: one Int,
	rightPart: one Int
}
{
	leftPart>=0
	rightPart>=0
}

abstract sig Date{
	day: one Int,
	month: one Int,
	year: one Int
}
{
	day>=1 and day<=31
	month>=1 and month<=12
	year>=1
}
sig SimpleDate extends Date{}
sig MeetingDate extends Date{
	time: one Time
}




//SIGNATURES


abstract sig User{}
sig Visitor extends User{}
sig RegisteredUser extends User{
	name: one Strings,
	surname: one Strings,
	mail: one Strings,
	address: one Strings,
	username: one Strings,
	password: one Strings,
	telephone: one Int,
	dateOfBirth: one SimpleDate,
	createdMeetings: set Meeting,
	createdBreaks: set Break,
	calendar: one Calendar,
	globalPreferences: one GlobalPreference
}

sig Calendar{
	trip: set Trip
}

abstract sig Break{
	name: one Strings,
	date: one SimpleDate,
	startingTime: one Time,
	endingTime: one Time,
	minimumDuration: one Time,
	location: set Location
}
sig LunchBreak extends Break{
	foodType: one Strings,
	maxPrice: one PositiveFloat
}
sig CoffeeBreak extends Break{}

sig Meeting{
	name: one Strings,
	date: one MeetingDate,
	duration: one Int,
	description: one Strings,
	location: one Location,
}
{
	duration>0
}
sig Location{
	address: one Strings,
	province: one Strings,
	city: one Strings,
	cap: one Int,
	country: one Strings
}
{
	cap>0
}

sig Trip{
	meetings: set Meeting,
	breaks: set Break,
	travelMeans: set TravelMeans,
	cost: one PositiveFloat,
	warning: set Warning,
	preference: set TripPreference,
}

sig Warning{
	type: one Strings,
	description: one Strings
}

abstract sig Preference{
	maxWalkingDistance: one PositiveFloat,
	minimizeFootPrint: one Boolean,
	maxPublicTransportationTime: one Time,
	blockedTravelMeans: set TravelMeans
}
sig TripPreference extends Preference{}
sig GlobalPreference extends Preference{
	lunchStart: one Time,
	lunchEnd: one Time
}

sig TravelMeans{
	type: one TravelMeansType,
	cost: one PositiveFloat,
	website: one Strings
}


//FACTS


//Every calendar belongs to exactly one user
fact OneCalendarPerRegisteredUser{
	all cal: Calendar | (one ru : RegisteredUser | ru.calendar = cal)
}

//Every travel means type belongs to exactly one travel means
fact OneTravelMeansTypePerTravelMeans{
	all tmt: TravelMeansType | (one tm : TravelMeans | tm.type = tmt)
}

//Every meeting is created by exactly one user
fact OneMeetingCreator{
	all mee: Meeting | (one ru : RegisteredUser | mee in ru.createdMeetings)
}

//Every break is created by exactly one user
fact OneBreakCreator{
	all br: Break | (one ru : RegisteredUser | br in ru.createdBreaks)
}

//Every warning belongs to exactly one user's trip
fact OneWarningPerTrip{
	all war: Warning | (one tr : Trip | tr.warning = war)
}

//Every day has exactly one trip associated
fact DayAndTripCorrispondence{
	all disj mee1, mee2: Meeting| 
		(one tr: Trip |
			(mee1 in tr.meetings) and (mee2 in tr.meetings) 
			and (mee1.date.day=mee2.date.day)
			and (mee1.date.month=mee2.date.month)
			and (mee1.date.year=mee2.date.year)
		)
}

//Every activity is associated to exactly one trip
fact ActivitiesAndTripCorrispondence{
	all disj tr1, tr2: Trip |
		tr1.meetings & tr2.meetings = none and tr1.breaks & tr2.breaks = none
}

//Every date belongs to exactly one activity (break or meeting)
fact OneDatePerActivity{
	all da: Date | 
		( 
			(one br : Break | br.date = da) or
			(one me: Meeting | me.date = da) or
			(one re: RegisteredUser | re.dateOfBirth=da)
		)
}

//All the meetings created by a registered user are present in his/her calendar
fact CreatedMeetingsInRegisteredUserCalendar{
		all ru: RegisteredUser |
			ru.createdMeetings in ru.calendar.trip.meetings
}

//All the global preferences are created by a registered user
fact GlobalPreferencesCreatedByUser{	
	all gp: GlobalPreference | (one ru : RegisteredUser | ru.globalPreferences = gp)
}

//All the breaks created by a registered user are present in his/her calendar
fact CreatedMeetingsInRegisteredUserCalendar{
		all ru: RegisteredUser | 
			ru.createdBreaks in ru.calendar.trip.breaks
}

//Prevents the use of the same username or email for more than one user
fact NoDuplicatedUser{
	no disj ru1, ru2: RegisteredUser | 
		(ru1.username = ru2.username) or (ru1.mail = ru2.mail)
}

//Every travel means type is unique (e.g. only one 'Taxi' type, only one 'Private car' type etc...)
fact NoDuplicatedMeansType{
	no disj tm1, tm2: TravelMeans | 
		(tm1.type =  tm2.type) 
}


//Travel means blocked in the global preferences cannot be used
//for the trips of the registered user
fact NoGloballyBlockedTravelMeansInTheTrips{
	all ru: RegisteredUser|
		ru.calendar.trip.travelMeans.type & ru.globalPreferences.blockedTravelMeans.type = none
}

//Travel means blocked in the trip preferences cannot be used
//for the current trip of the registered user
fact NoBlockedTravelMeansInTheTrips{
	all tr: Trip | 
		tr.travelMeans.type not in tr.preference.blockedTravelMeans.type
}

//If a user inserts two (or more) meeting with an overlapping time, there must be
//(at least) a warning in the trip associated to the meetings
fact GenerateWarningWithOverlappingMeetingTime{
	all tr: Trip, mee1, mee2: Meeting | 
		((mee1 in tr.meetings) and 
		(mee2 in tr.meetings) and 
			((mee1.date.time.hour.add[mee1.duration] > mee2.date.time.hour) or 
				(
					(mee1.date.time.hour.add[mee1.duration] = mee2.date.time.hour) and
					(mee1.date.time.minute > mee2.date.time.minute)
				)
			))
		implies 
		(#tr.warning>=1)
}

//If a user inserts two (or more) breaks with an overlapping time, then there must be
//(at least) a warning in the trip associated to the meetings
fact GenerateWarningWithOverlappingBreakTime{
	all tr: Trip, br1, br2: Break | 
		((br1 in tr.breaks) and 
		(br2 in tr.breaks) and 
			(br1.endingTime.hour > br2.startingTime.hour or
				(br1.endingTime.hour = br2.startingTime.hour and
				(br1.endingTime.minute > br2.startingTime.minute)
			))
		)
		implies 
		(#tr.warning>=1)
}




//ASSERTIONS


//Check that there all the calendars are created by a registered user
assert NoCalendarWithoutUser{
	no cal: Calendar | 
		(no ru : RegisteredUser | 
			ru.calendar = cal)
}

check NoCalendarWithoutUser

//Check that all the meetings created by a registered user are present in his/her calendar
assert AllMeetingsAreInTheMeetingCreatorCalendar{
	no ru: RegisteredUser | 
		ru.createdMeetings not in ru.calendar.trip.meetings
}

check AllMeetingsAreInTheMeetingCreatorCalendar

//Check that all the breaks created by a registered user are present in his/her calendar
assert AllBreaksAreInTheMeetingCreatorCalendar{
	no ru: RegisteredUser |
		ru.createdBreaks not in ru.calendar.trip.breaks
}

check AllBreaksAreInTheMeetingCreatorCalendar

//Check that all the travel means selected as "blocked" by the registered user
//in the global preferences don't appear in the trip's travel means
assert AllTheMeansUsedForATripAreNotGloballyBlocked{
	no ru: RegisteredUser| 
		ru.calendar.trip.travelMeans.type in ru.globalPreferences.blockedTravelMeans.type
}

check AllTheMeansUsedForATripAreNotGloballyBlocked
//Check that all the travel means selected as "blocked" by the registered user
//for a specific trip don't appear in the trip's travel means
assert AllTheMeansUsedForATripAreNotBlocked{
	no tr: Trip |
		tr.travelMeans.type in tr.preference.blockedTravelMeans.type
}

check AllTheMeansUsedForATripAreNotBlocked


//PREDICATES


//This predicate show that if a registered user specify in his/her preference that a 
//certain travel means type is blocked, it will not be used in the meeting's travel means
pred showBlockedTravelMeansInMeetings(){
	#RegisteredUser=1
	#Trip=1
	#Meeting=1
	#Break=0
	#TravelMeansType=2
	#(GlobalPreference.blockedTravelMeans)=1
	}
run showBlockedTravelMeansInMeetings for 4 but 7 int

//This predicate show that if two meetings have an overlapping time, then (at least) one
//warning associated to the trip that contains the two meetings is generated
pred showWarningWithOverlappingTime(){
	#RegisteredUser=1
	#Trip=1
	#Meeting=2
	#Break=0
	#TravelMeansType=2
	#Time=1 //The two meetings starts at the same time
	}
run showWarningWithOverlappingTime for 4 but 7 int

//This predicate show a simplified instance of the world
pred showWorld(){
	#RegisteredUser=1
	#Trip=1
	#Meeting=1
	#Break=1
	#TravelMeansType=2
	}
run showWorld for 4 but 7 int
