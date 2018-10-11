#################
## Kevin Fahey ##
#################

###############################
## Prepared April 25, 2018   ##
###############################

#######################################
## Determinants of Incumbency Effect ##
## Electoral Reforms and The Impacts ##
#######################################


######################
## Clear Everything ##
######################

rm(list=ls())

###########################
## set working directory ##
###########################

# set working directory here #

####################
## load libraries ##
####################

library(foreign)
library(sandwich)
library(lme4)
library(effects)
library(Matching)
library(rgenoud)
library(car)
library(cem)
library(arm)
library(lattice)
library(plm)
library(stargazer)
library(aod)
library(ggplot2)
library(compactr)
library(MASS)
library(stats)
library(xtable)
library(RColorBrewer)
library(systemfit)
library(plyr)
library(dplyr)
library(rdd)
library(Amelia)
library(haven)
library(zoo)
library(remotes)
library(foreach)
library(data.table)
library(latticeExtra)
library(RColorBrewer)
library(classInt)
library(mapproj)
library(maps)
library(maptools)
library(googleVis)
library(sp)
library(fiftystater)
library(grDevices)
options(scipen=7)
options(digits=4)


##############################
## load ClusterMod function ##
## for cluster std. errors  ##
##############################

clusterMod<-function(model, cluster)
{
  require(multiwayvcov)
  require(lmtest)
  vcovCL<-cluster.vcov(model, cluster)
  
  coef<-coeftest(model, vcovCL)
  #w<-waldtest(model, vcov = vcovCL, test = "F")
  get_confint<-function(model, vcovCL){
    t<-qt(.975, model$df.residual)
    ct<-coeftest(model, vcovCL)
    cse<-sqrt(diag(vcovCL))
    est<-cbind(ct[,1], cse,ct[,1]-t*ct[,2], ct[,1]+t*ct[,2])
    colnames(est)<-c("Estimate", "Clustered SE","LowerCI","UpperCI")
    return(est)
  }
  ci<-round(get_confint(model, vcovCL),4)
  return(list(coef, ci))
}


###################################
## Use Function to Generate Lags ##
###################################

do_lag <- function(the_data, variables, num_periods) {
  num_vars <- length(variables)
  num_rows <- nrow(the_data)
  
  for (j in 1:num_vars) {
    for (i in 1:num_periods) {
      the_data[[paste0(variables[j], i)]] <- c(rep(NA, i), head(the_data[[variables[j]]], num_rows - i))
    }
  }
  
  return(the_data)
}


##################
## Main Dataset ##
##################

# dat <- read_dta("/Backup/Dropbox/Dissertation/Chapter 3/RDD Term Limits/Myth 7-27-2016.dta") # See do-file for trimming data in Stata

dat <- read_dta("~/carseyberry 7-27-2016.dta") # 308125 obs #


##################################################
## Trim Dataset To Remove Unneeded Observations ##
##################################################

dat <- dat[which(dat$V21 == 100),] # only Dems, 152050 obs #
dat <- dat[which(dat$V07 == 9),] # Remove upper house, Nebraska, 122275 obs #
dat <- dat[which(dat$V06 == 11),] # Remove elections not held in November (98160 obs) #
dat <- dat[which(dat$V12 == 1),] # Remove multimember dist (71494 obs)


##################################
## Remove Unnecessary Variables ##
##################################

dat <- dat[,c("CASEID", "V01", "V02", "V03", "V05", "V09", "V11", "V12", "V13", "V16", "V17",
              "V18", "V19", "V20", "V21", "V22", "V23", "V24", "V25", "V29","V30", "V31", "V35",
              "V36")]

###############################
## Create Lag of Vote Margin ##
## And Incumbency            ##
###############################

dat$votemarg <- dat$V23/dat$V29
dat$incumbent <- dat$V22


####################################
## Try The DPLYR Lag Method       ##
## Lag vote share, tt vote share, ##
## incumbency, winning            ##
####################################

# generate unique id for each district #
dat$uniq.dist <- as.numeric(paste((dat$V01 * 100), dat$V09, sep = ""))

# sort data #
dat <- dat[order(dat$V01, dat$V09, dat$V05),]

# votelag #
dat <- dat %>% 
       group_by(uniq.dist) %>%
       mutate(lag.value = dplyr::lag(votemarg, n = 1, default = NA))
dat$votelag <- dat$lag.value

# inclag #
dat <- dat %>% 
       group_by(uniq.dist) %>%
       mutate(lag.value = dplyr::lag(incumbent, n = 1, default = NA))
dat$inclag <- dat$lag.value

# wonlag #
dat <- dat %>% 
  group_by(uniq.dist) %>%
  mutate(lag.value = dplyr::lag(V24, n = 1, default = NA))
dat$wonlag <- dat$lag.value

#####################################
## Now Create Two-Party Vote Share ##
#####################################

dat$ttvotemarg <- dat$V30/(dat$V30 + dat$V31)

# and its lag #
dat <- dat %>% 
  group_by(uniq.dist) %>%
  mutate(lag.value = dplyr::lag(ttvotemarg, n = 1, default = NA))
dat$ttvotelag <- dat$lag.value

#############################################################
## create year and state variable names for ease of memory ##
#############################################################

dat$year<-as.numeric(dat$V05)
dat$state<-as.numeric(dat$V03)
dat$statyr<-dat$year*100+dat$state


####################################################
## Read in Fouirnaies Campaign Contributions Data ##
####################################################

# accesscont.dat <- read_dta("~/How_Do_interest_Groups_Seek_Access_to_Committees.dta") Alex Fouirnaies' data can be found on his Harvard Dataverse page #

# agendaset.dat <- read_dta("~/When Are Agenda-Setters Valuable/when_are_agenda_setters_valuable.dta") Alex Fouirnaies' data can be found on his Harvard Dataverse page #

##################################
## Add in state population data ##
##################################

statyr <- read.csv("~/2017-10-24 statyr.csv")
statyr <- statyr[order(statyr$year, statyr$scode),]

#################################
## statyr linear interpolation ##
## have to do by state         ##
#################################

master.interpolate <- matrix(NA, nrow = 56, ncol = 31)

for(i in 1:56){
  
  temp.dat <- statyr[statyr$scode == i,]
  
  if(nrow(temp.dat) == 0) next
  
  master.interpolate[i,] <- na.approx(temp.dat$staffsize)
  
}

master.interpolate <- na.omit(master.interpolate)

master.interpolate.2 <- as.vector(master.interpolate)

statyr$staff.linear <- c(rep(NA, 588), master.interpolate.2, rep(NA, 294))


####################
## Merge Datasets ##
####################

full <- merge(dat, statyr, by.x="statyr", by.y="statyr", all.x=T)


###############################
## Generate Term Limits Data ##
###############################

## Taken from NCSL Website On Term Limits ##
# http://www.ncsl.org/research/about-state-legislatures/chart-of-term-limits-states.aspx #

## Ariz = 3, Ark = 4, Calif = 5, Colo = 6, Florida = 9, ##
## Louisiana = 18, Maine = 19, Mich = 22, Missou = 25, ##
## Mont = 26, Nevada = 28, Ohio = 35, Oklah = 36, ##
## South Dakota == 41 ##

## Idaho = 12, Mass = 21, Oregon = 37, Utah = 44, Wash = 47, Wyo = 50 ##


# pre term limits data #
# states that eventually adopted or implemented term limits #
full$pretl <- ifelse(full$V01 == 3 | full$V01 == 4 | full$V01 == 5 |
                    full$V01 == 6 | full$V01 == 9 | full$V01 == 12 |
                    full$V01 == 18 | full$V01 == 19 | full$V01 == 21 |
                    full$V01 == 22 | full$V01 == 25 | full$V01 == 26 |
                    full$V01 == 28 | full$V01 == 35 | full$V01 == 36 |
                    full$V01 == 37 | full$V01 == 41 | full$V01 == 44 |
                    full$V01 == 47 | full$V01 == 50,
                    1, 0) # 20 states (Nebraska would make 21) #

full$pre90 <- ifelse(full$pretl == 1 & full$V01 < 1990, 1, 0)

# contemporary term limits information #
# term limits adopt #
# years with term limits to today #
full$termlimitsadopt <- 0
full$termlimitsadopt[full$V01 == 3 & full$V05 >= 1992] <- 1
full$termlimitsadopt[full$V01 == 4 & full$V05 >= 1992] <- 1
full$termlimitsadopt[full$V01 == 5 & full$V05 >= 1990] <- 1
full$termlimitsadopt[full$V01 == 6 & full$V05 >= 1990] <- 1
full$termlimitsadopt[full$V01 == 9 & full$V05 >= 1992] <- 1
full$termlimitsadopt[full$V01 == 18 & full$V05 >= 1995] <- 1
full$termlimitsadopt[full$V01 == 19 & full$V05 >= 1993] <- 1
full$termlimitsadopt[full$V01 == 22 & full$V05 >= 1992] <- 1
full$termlimitsadopt[full$V01 == 25 & full$V05 >= 1992] <- 1
full$termlimitsadopt[full$V01 == 26 & full$V05 >= 1992] <- 1
full$termlimitsadopt[full$V01 == 28 & full$V05 >= 1996] <- 1
full$termlimitsadopt[full$V01 == 35 & full$V05 >= 1992] <- 1
full$termlimitsadopt[full$V01 == 36 & full$V05 >= 1990] <- 1
full$termlimitsadopt[full$V01 == 41 & full$V05 >= 1992] <- 1

# those that repealed term limits #
full$termlimitsadopt[full$V01 == 12 & full$V05 >= 1994 & full$V05 < 2002] <- 1
full$termlimitsadopt[full$V01 == 21 & full$V05 >= 1994 & full$V05 < 1997] <- 1
full$termlimitsadopt[full$V01 == 37 & full$V05 >= 1992 & full$V05 < 2002] <- 1
full$termlimitsadopt[full$V01 == 44 & full$V05 >= 1994 & full$V05 < 2003] <- 1
full$termlimitsadopt[full$V01 == 47 & full$V05 >= 1992 & full$V05 < 1998] <- 1
full$termlimitsadopt[full$V01 == 50 & full$V05 >= 1992 & full$V05 < 2004] <- 1


# term limits implement #
full$termlimitsimplement <- 0
# year implemented #
full$termlimitsimplement[full$V01 == 3 & full$V05 >= 2000] <- 1
full$termlimitsimplement[full$V01 == 4 & full$V05 >= 1998] <- 1
full$termlimitsimplement[full$V01 == 5 & full$V05 >= 1996] <- 1
full$termlimitsimplement[full$V01 == 6 & full$V05 >= 1998] <- 1
full$termlimitsimplement[full$V01 == 9 & full$V05 >= 2000] <- 1
full$termlimitsimplement[full$V01 == 18 & full$V05 >= 2007] <- 1
full$termlimitsimplement[full$V01 == 19 & full$V05 >= 1996] <- 1
full$termlimitsimplement[full$V01 == 22 & full$V05 >= 1998] <- 1
full$termlimitsimplement[full$V01 == 25 & full$V05 >= 2002] <- 1
full$termlimitsimplement[full$V01 == 26 & full$V05 >= 2000] <- 1
full$termlimitsimplement[full$V01 == 28 & full$V05 >= 2010] <- 1
full$termlimitsimplement[full$V01 == 35 & full$V05 >= 2000] <- 1
full$termlimitsimplement[full$V01 == 36 & full$V05 >= 2004] <- 1
full$termlimitsimplement[full$V01 == 41 & full$V05 >= 2000] <- 1


###############################
## fix dataset to remove NAs ##
###############################

dat1 <- as.data.frame(cbind(full[,c("V01", "V02", "V03", "CASEID", "ttvotelag", "ttvotemarg", 
                                  "wonlag", "termlimitsadopt", 
                                  "termlimitsimplement", "pre90", "pretl", 
                                  "V05", "V29", "staffsize", "chambersize", 
                                  "populationofstate", "staffstep", "V22", 
                                  "V09", "personalstaff", "staff.linear", "inclag",
                                  "uniq.dist", "V18")]))

names(dat1) <- c("state", "statename", "statefips", "caseid", "votelag", 
               "votemarg", "wonlag", "termlimitsadopt", 
               "termlimitsimplement", "pre90", "pretl", "year", "totvotes", 
               "staffsize", "chambersize", "statpop", "staffstep", 
               "incumbent", "district", "personalstaff", "stafflinear", "inclag",
               "uniq.dist", "candid")

dat1$year <- as.numeric(dat1$year)
dat1$totvotes <- as.numeric(dat1$totvotes)
dat1$staffsize <- as.numeric(dat1$staffsize)
dat1$staffstep <- as.numeric(dat1$staffstep)
dat1$stafflinear <- as.numeric(dat1$stafflinear)
dat1$chambersize <- as.numeric(dat1$chambersize)
dat1$statpop <- as.numeric(dat1$statpop) ## NAs introduced by coercion ##
dat1$incumbent <- as.numeric(dat1$incumbent)
dat1$state <- as.numeric(dat1$state)
dat1$district <- as.numeric(dat1$district)
dat1$staffpop <- dat1$stafflinear/(dat1$statpop/100000) ## state population in 100000s ##


########################################
## Sort Dat1 by state, year, district ##
########################################

dat1 <- dat1[order(dat1$statefips, dat1$district, dat1$year),]


###################
## Lag Variables ##
## For Staffing  ##
###################

# staffpop1 #
dat1 <- dat1 %>% 
  group_by(uniq.dist) %>%
  mutate(lag.value = dplyr::lag(staffpop, n = 1, default = NA))
dat1$staffpop1 <- dat1$lag.value

# termlimitsadopt1 #  
dat1 <- dat1 %>% 
  group_by(uniq.dist) %>%
  mutate(lag.value = dplyr::lag(termlimitsadopt, n = 1, default = NA))
dat1$termlimitsadopt1 <- dat1$lag.value

# termlimitsimplement1 #
dat1 <- dat1 %>% 
  group_by(uniq.dist) %>%
  mutate(lag.value = dplyr::lag(termlimitsimplement, n = 1, default = NA))
dat1$termlimitsimplement1 <- dat1$lag.value


##################################
## Difference Staffing Variable ##
## And Term Limits Variables    ##
##################################

dat1$staffdiff <- dat1$staffpop -  dat1$staffpop1
dat1$tla.diff <- dat1$termlimitsadopt - dat1$termlimitsadopt1
dat1$tli.diff <- dat1$termlimitsimplement - dat1$termlimitsimplement1


#######################################################
############## BEGIN ANALYSIS #########################
#######################################################


##################################################
## Create Term-Limits Data to Remove Staff Data ##
## Staffing Data Have NAs 1967-1979, 2010       ##
##################################################

tl.dat <- dat1[,c("caseid", "votelag", "votemarg", "wonlag",
                  "termlimitsadopt", "termlimitsimplement",
                  "pre90", "pretl", "year", "totvotes",
                  "incumbent", "state", "district",
                  "termlimitsadopt1", "termlimitsimplement1",
                  "tla.diff", "tli.diff")]


#####################################################
## Next, full three-way interactions of RD designs ##
#####################################################

dat90 <- tl.dat[tl.dat$year >= 1990,] # 36975 obs

w <- dat90$wonlag
xc <- dat90$votelag-0.5
tl <- dat90$termlimitsadopt 
y <- dat90$votemarg


rd.1 <- lm(y ~ w * xc * tl)
summary(rd.1)
se.rd.1 <- sqrt(diag(vcovHC(rd.1)))


##################
## And pre-1990 ##
##################

dat88 <- tl.dat[tl.dat$year <= 1988,] ## 34436 obs

w <- dat88$wonlag
xc <- dat88$votelag-0.5
tl <- dat88$pretl 
y <- dat88$votemarg


rd.2 <- lm(y ~ w * xc * tl)
summary(rd.2)
se.rd.2 <- sqrt(diag(vcovHC(rd.2)))

stargazer(rd.1, rd.2, se = list(se.rd.1, se.rd.2), no.space = T)


######################################################
## Create term-limited and non-term limited subsets ##
######################################################

dat.t <- na.omit(tl.dat[which(tl.dat$termlimitsadopt == 1 & tl.dat$year >= 1990),]) # 9543 obs #
dat.nt <- na.omit(tl.dat[which(tl.dat$termlimitsadopt == 0 & tl.dat$year >= 1990),]) # 25377 obs #

###############################################################
## Use RDEstimate to obtain RD estimates, optimal bandwidths ##
###############################################################

rd.t <- RDestimate(votemarg ~ votelag, data = dat.t, cutpoint = 0.5)
summary(rd.t) # optimal bandwidth 0.1249, obs 4456 # # est 0.0790 #

rd.nt <- RDestimate(votemarg ~ votelag, data = dat.nt, cutpoint = 0.5)
summary(rd.nt) # optimal bandwidth 0.1342, obs 9541 ## est 0.0705 #


#####################################
## Manual Estimation of RD effects ##
#####################################

## move to optimal bandwidth ##

dat.t <- dat.t[which(dat.t$votelag >= 0.5 - rd.t$bw[1] & dat.t$votelag <= 0.5 + rd.t$bw[1]),] # 4456 obs #

## generate variable names ##

w <- dat.t$wonlag
xc <- dat.t$votelag-0.5
tl <- dat.t$termlimitsadopt # should always = 1 #
y <- dat.t$votemarg

## estimate ##

mt <- lm(y~w*xc)
est.mt <- mt$coef[2] # 0.0767 #
se.mt <- sqrt(diag(vcovHC(mt)))[2] # 0.0076 #


b <- seq(from = 0.001, to = 0.999, by = .0035) # generates binwidths #
mid <- seq(from = 0.003, to = 0.997, by = .0035) # generates midpoints #
count <- rep(NA,length(mid))
m <- 1

for(m in 1:length(count)) {
  sel <- which((xc+0.5) > b[m] & (xc+0.5) <= b[(m+1)])
  count[m] <- mean(y[sel]) # generates average value of y in bin #
}


###############################################
## FIGURE 3A: RD Effect, Term-Limited States ##
###############################################

par(pty = "s")
plot(mid-0.5, count, xlab = "Vote Share - 0.50 in First Election", ylab = "Vote Share in Next Election", cex.lab = 1.3, cex.axis = 1.3, pch = 19, col = "grey", main="RD Effect, Term-Limited States", sub = "", xlim=c(-rd.t$bw[1], rd.t$bw[1]), ylim=c(0.2,0.8))
x.plot <- seq(from = -rd.t$bw[1], to = 0, length.out = 1000)
y.plot <- mt$coef[1] +
  mt$coef[3] * x.plot

x.plotz <- seq(from = 0, to = rd.t$bw[1], length.out = 1000)
y.plotz <- mt$coef[1] +
  mt$coef[2] +
  mt$coef[3] * x.plotz +
  mt$coef[4] * x.plotz 

lines(x = x.plot, y = y.plot, col = "black", lwd = 4, lty = 3)
lines(x = x.plotz, y = y.plotz, col = "black", lwd = 4, lty = 3)
lines(x = c(0,0), y = c(y.plot[1000],y.plotz[1]), col = "black", lwd = 4)
text(x = -0.014, y = 0.67, bquote(widehat(tau)[RDD]^sharp == .(est.mt)~(0.008)), col = "black", cex = 1.2)


########################################
##### Without Term Limits, Same    #####
########################################

#######################
## estimate manually ##
#######################

dat.nt <- dat.nt[which(dat.nt$votelag >= 0.5 - rd.nt$bw[1] & dat.nt$votelag <= 0.5 + rd.nt$bw[1]),] # 9541 obs #

## generate variable names ##

y <- dat.nt$votemarg
xc <- dat.nt$votelag-0.5
w <- dat.nt$wonlag

## estimate ##

mnt <- lm(y~w*xc, data=dat.nt)
est.nt <- mnt$coef[2] # 0.0866 #
se.nt <- sqrt(diag(vcovHC(mnt)))[2] # 0.0064 #

b <- seq(from = 0.001, to = 0.999, by = .0025) # generates binwidths #
mid <- seq(from = 0.003, to = 0.997, by = .0025) # generates midpoints #
count <- rep(NA,length(mid))
m <- 1

for(m in 1:length(count)) {
  sel <- which((xc+0.5) > b[m] & (xc+0.5) <= b[(m+1)])
  count[m] <- mean(y[sel]) # generates average value of y in bin #
}


###################################################
## FIGURE 3B: RD Effect, Non Term-Limited States ##
###################################################

par(pty = "s")
plot(mid-0.5, count, xlab = "Vote Share - 0.50 in First Election", ylab = "Vote Share in Next Election", cex.lab = 1.3, cex.axis = 1.3, pch = 19, col = "grey", main="RD Effect, Non-Term-Limited States", sub = "", xlim=c(-rd.nt$bw[1], rd.nt$bw[1]), ylim=c(0.2,0.8))
x.plot <- seq(from = -rd.nt$bw[1], to = 0, length.out = 1000)
y.plot <- mnt$coef[1] +
  mnt$coef[3] * x.plot

x.plotz <- seq(from = 0, to = rd.nt$bw[1], length.out = 1000)
y.plotz <- mnt$coef[1] +
  mnt$coef[2] + 
  mnt$coef[3] * x.plotz +
  mnt$coef[4] * x.plotz

lines(x = x.plot, y = y.plot, col = "black", lwd = 4, lty = 3)
lines(x = x.plotz, y = y.plotz, col = "black", lwd = 4, lty = 3)
lines(x = c(0,0), y = c(y.plot[1000],y.plotz[1]), col = "black", lwd = 4)
text(x = -0.014, y = 0.67, bquote(widehat(tau)[RDD]^sharp == .(est.nt)~(0.006)), col = "black", cex = 1.2)


####################################
####################################
####################################


#####################################################################
## Examine RDD before 1990, compare term limits to not term limits ##
#####################################################################


################# This means estimating for states that 
## Term limits ## eventually adopted term limits
################# but estimating before 1990

dat.ptl <- na.omit(tl.dat[which(tl.dat$pretl == 1 & tl.dat$year < 1990),]) # 10886 obs #

rd.ptl <- RDestimate(votemarg ~ votelag, data = dat.ptl, cutpoint = 0.5)
summary(rd.ptl) # bw 0.1245, obs 4331 # # est 0.0563 #


###########################
## Now estimate manually ##
###########################

dat.ptl <- dat.ptl[which(dat.ptl$votelag >= 0.5 - rd.ptl$bw[1] & dat.ptl$votelag <= 0.5 + rd.ptl$bw[1]),] # 4331 obs #

y <- dat.ptl$votemarg
xc <- dat.ptl$votelag - 0.5
w <- dat.ptl$wonlag

pt <- lm(y ~ w * xc, data = dat.ptl)
summary(pt)

## estimate ##

est.pt <- pt$coef[2] # 0.0636
se.pt <- sqrt(diag(vcovHC(pt)))[2] # 0.010

b <- seq(from = 0.001, to = 0.999, by = .0035) # generates binwidths #
mid <- seq(from = 0.003, to = 0.997, by = .0035) # generates midpoints #
count <- rep(NA,length(mid))
m <- 1

for(m in 1:length(count)) {
  sel <- which((xc+0.5) > b[m] & (xc+0.5) <= b[(m+1)])
  count[m] <- mean(y[sel]) # generates average value of y in bin #
}


##############################################
## FIGURE 4A: PRE-1990, TERM-LIMITED STATES ##
##############################################

par(pty = "s")
plot(mid-0.5, count, xlab = "Vote Share - 0.50 in First Election", ylab = "Vote Share in Next Election", cex.lab = 1.3, cex.axis = 1.3, pch = 19, col = "grey", main="RD Effect, Term-Limited States (pre-1990)", sub = "", xlim=c(-rd.ptl$bw[1], rd.ptl$bw[1]), ylim=c(0.2,0.8))
x.plot <- seq(from = -rd.ptl$bw[1], to = 0, length.out = 1000)
y.plot <- pt$coef[1] +
  pt$coef[3] * x.plot

x.plotz <- seq(from = 0, to = rd.ptl$bw[1], length.out = 1000)
y.plotz <- pt$coef[1] +
  pt$coef[2] +
  pt$coef[3] * x.plotz +
  pt$coef[4] * x.plotz 

lines(x = x.plot, y = y.plot, col = "black", lwd = 4, lty = 3)
lines(x = x.plotz, y = y.plotz, col = "black", lwd = 4, lty = 3)
lines(x = c(0,0), y = c(y.plot[1000],y.plotz[1]), col = "black", lwd = 4)
text(x = -0.014, y = 0.67, bquote(widehat(tau)[RDD]^sharp == .(est.pt)~(0.010)), col = "black", cex = 1.2)


##################### Here I estimate states that never
## Not Term Limits ## adopted term limits before 1990
##################### as a comparison group

dat.pntl <- na.omit(tl.dat[which(tl.dat$pretl == 0 & tl.dat$year < 1990),]) # 17809 obs #

rd.pntl <- RDestimate(votemarg ~ votelag, data = dat.pntl, cutpoint = 0.5)
summary(rd.pntl) # bw 0.1679, obs 8897, est 0.0622 #

## estimate manually ##

dat.pntl <- dat.pntl[which(dat.pntl$votelag >= 0.5 - rd.pntl$bw[1] & dat.pntl$votelag <= 0.5 + rd.pntl$bw[1] ),] # 8897 obs #

## estimate ##

y <- dat.pntl$votemarg
xc <- dat.pntl$votelag - 0.5
w <- dat.pntl$wonlag

pnt <- lm(y ~ w * xc)

est.pnt <- pnt$coef[2] # 0.0693
se.pnt <- sqrt(diag(vcovHC(pnt)))[2] # 0.0062

b <- seq(from = 0.001, to = 0.999, by = .0035) # generates binwidths #
mid <- seq(from = 0.003, to = 0.997, by = .0035) # generates midpoints #
count <- rep(NA,length(mid))
m <- 1

for(m in 1:length(count)) {
  sel <- which((xc+0.5) > b[m] & (xc+0.5) <= b[(m+1)])
  count[m] <- mean(y[sel]) # generates average value of y in bin #
}


##################################################
## FIGURE 4A: PRE-1990, NON TERM-LIMITED STATES ##
##################################################

par(pty = "s")
plot(mid-0.5, count, xlab = "Vote Share - 0.50 in First Election", ylab = "Vote Share in Next Election", cex.lab = 1.3, cex.axis = 1.3, pch = 19, col = "grey", main="RD Effect, Non Term-Limited States (pre-1990)", sub = "", xlim=c(-rd.pntl$bw[1], rd.pntl$bw[1]), ylim=c(0.2,0.8))
x.plot <- seq(from = -rd.pntl$bw[1], to = 0, length.out = 1000)
y.plot <- pnt$coef[1] +
  pnt$coef[3] * x.plot

x.plotz <- seq(from = 0, to = rd.pntl$bw[1], length.out = 1000)
y.plotz <- pnt$coef[1] +
  pnt$coef[2] +
  pnt$coef[3] * x.plotz +
  pnt$coef[4] * x.plotz 

lines(x = x.plot, y = y.plot, col = "black", lwd = 4, lty = 3)
lines(x = x.plotz, y = y.plotz, col = "black", lwd = 4, lty = 3)
lines(x = c(0,0), y = c(y.plot[1000],y.plotz[1]), col = "black", lwd = 4)
text(x = -0.014, y = 0.67, bquote(widehat(tau)[RDD]^sharp == .(est.pnt)~(0.006)), col = "black", cex = 1.2)


################################################
## Comparison of the reform, before and after ##
## Using RDestimate technique, not manual     ##
################################################

rd.t$est[1] - rd.nt$est[1] # compares term limits to not term limits, post-1990 #

rd.ptl$est[1] - rd.pntl$est[1] # compares prospective term-limits to prospective not, pre-1990 #

rd.t$est[1] - rd.ptl$est[1] # compares term limits before and after #

rd.nt$est[1] - rd.pntl$est[1] # compares not term limits before and after #


#############################################
## Compare RDestimate to Manual Estimation ##
#############################################

rd.t$est[1] - est.mt[1] # term limits, post-1990 # # 0.00199 #

rd.ptl$est[1] - est.pt[1] # term limits, pre-1990 # # -0.00311 #

rd.nt$est[1] - est.nt[1] # not term limits, post-1990 # # -0.00722 #

rd.pntl$est[1] - est.pnt[1] # not term limits, pre-1990 # # -0.00672 #


###################################
## Now, Create a Plot of the DiD ##
## Use RD Estimates to Create    ##
## The Annual Incumbency Effect  ##
###################################


#########################################################
## First, we need to create an annual averaged measure ##
#########################################################

## Create output frame ##
dat.annual.did <- matrix(NA, nrow = 2010, ncol = 7)


## Generate DiD estimates, ses ##
foreach(i = c(seq(from = 1968, to = 2010, by = 2))) %do% { ## by integrating odd-numbered years into even-numbered years as a whole election cycle, I eliminate some major problems. Odd years had absurdly-high re-election rates (many at 0.999 or 1 vote share) which meant it wasn't as useful to show parallel trends. Some odd years do not have sufficient cases to run an RD ##
  
  dat.year <- tl.dat[tl.dat$year == i | tl.dat$year == i-1,] # the election cycle # 
  
  # estimate with RDestimate to obtain bandwidth (NOT ENOUGH OBS) #
  #rde.y.tl <- RDestimate(votemarg ~ votelag, data = dat.year.tl, cutpoint = 0.5)
  #rde.y.ntl <- RDestimate(votemarg ~ votelag, data = dat.year.ntl, cutpoint = 0.5)
  
  
  # gen dat states that adopt tl #
  dat.year.tl <- dat.year[dat.year$pretl == 1,] 
  
  # gen dat states that do not #
  dat.year.ntl <- dat.year[dat.year$pretl == 0,] 
  
  
  # generate covariates for rd #
  y.tl <- dat.year.tl$votemarg 
  xc.tl <- dat.year.tl$votelag - 0.5
  w.tl <- dat.year.tl$wonlag
  
  y.ntl <- dat.year.ntl$votemarg
  xc.ntl <- dat.year.ntl$votelag - 0.5
  w.ntl <- dat.year.ntl$wonlag
  
  # estimate rd #
  m.tl.y <- lm(y.tl ~ w.tl * xc.tl)
  m.ntl.y <- lm(y.ntl ~ w.ntl * xc.ntl)
  
  # save estimates and ses #
  dat.annual.did[i,1] <- m.tl.y$coefficients[[2]]
  dat.annual.did[i,2] <- sqrt(diag(vcovHC(m.tl.y)))[[2]]
  dat.annual.did[i,3] <- m.ntl.y$coefficients[[2]]
  dat.annual.did[i,4] <- sqrt(diag(vcovHC(m.ntl.y)))[[2]]
  dat.annual.did[i,5] <- i
  dat.annual.did[i,6] <- dim(dat.year.tl)[1]
  dat.annual.did[i,7] <- dim(dat.year.ntl)[1]

}


plot.dat <- as.data.frame(na.omit(dat.annual.did))
colnames(plot.dat) <- c("EstTL", "SETL", "EstNTL", 
                        "SENTL", "Year", "TLObs", "NTLObs")
xtable(plot.dat)

#############################################
## Generate Confidence Intervals, plot.dat ##
#############################################

plot.dat$TL.upr <- plot.dat$EstTL + (1.96 * (plot.dat$SETL/sqrt(22)))
plot.dat$TL.lwr <- plot.dat$EstTL - (1.96 * (plot.dat$SETL/sqrt(22)))

plot.dat$NTL.upr <- plot.dat$EstNTL + (1.96 * (plot.dat$SENTL/sqrt(22)))
plot.dat$NTL.lwr <- plot.dat$EstNTL - (1.96 * (plot.dat$SENTL/sqrt(22)))

plot.dat <- plot.dat[which(plot.dat$Year >= 1970),] # Remove 1967-1968 where inc effect was -0.18 #

###############
## DiD Plots ##
###############
span = 0.43

xyplot(EstTL ~ Year, data = plot.dat,
       aspect = 1,
       ylim = c(-0.05, 0.23),
       ylab = "Incumbency Effect",
       panel = function(x, y){
         # Term Limited RD Estimates #
         panel.xyplot(plot.dat$Year, plot.dat$EstTL,
                      col = "black", pch = 17)
         panel.loess(plot.dat$Year, plot.dat$EstTL,
                     lty = 6, lwd = 4, col = "black", span = span)
         # Confidence Intervals #
         panel.loess(plot.dat$Year, plot.dat$TL.upr,
                     lty = 3, col = "black", span = span)
         panel.loess(plot.dat$Year, plot.dat$TL.lwr,
                     lty = 3, col = "black", span = span)
         # Not-Term Limited RD Estimates #
         panel.xyplot(plot.dat$Year, plot.dat$EstNTL,
                      lty = 3, col = "black", pch = 16)
         panel.loess(plot.dat$Year, plot.dat$EstNTL,
                     lty = 3, lwd = 4, col = "black", 
                     family = "symmetric", span = span)
         # Confidence Intervals #
         panel.loess(plot.dat$Year, plot.dat$NTL.upr,
                     lty = 3, col = "black", span = span)
         panel.loess(plot.dat$Year, plot.dat$NTL.lwr,
                     lty = 3, col = "black", span = span)
         # Ablines for Critical Years #
         panel.abline(v = 1980, lwd = 2.5, lty = 3,
                      col = "black")
         panel.abline(v = 1990, lwd = 2.5, lty = 3,
                      col = "black")
         panel.abline(v = 2000, lwd = 2.5, lty = 3,
                      col = "black")
       },
       key = list(text = list(text = c("Term Limits", 
                                       "Without Term Limits"), cex = 1.25),
                  points = list(pch = c(17, 16), col = c("black", "black"), cex = .75),
                  lines = list(lty = c(6, 3), col = c("black", "black"), cex = 1),
                  space = "top", border = T, padding.text = 2.5)
       ) # histogram that plots all even years # # span really matters #


#############################
## Let's compare 1968-1990 ##
## versus 1990-2010        ##
#############################

plot.dat.88 <- plot.dat[plot.dat$Year <= 1988,]
plot.dat.90 <- plot.dat[plot.dat$Year >= 1990,]


## Plot Subsets, Separate Slopes ##

xyplot(EstTL ~ Year, data = plot.dat,
       aspect = 1,
       ylim = c(-0.05, 0.23),
       panel = function(x, y){
         
         # Term Limits, Pre-1990 #
         panel.xyplot(plot.dat.88$Year, plot.dat.88$EstTL,
                      col = "black", pch = 17)
         panel.loess(plot.dat.88$Year, plot.dat.88$EstTL,
                     lty = 6, lwd = 3, col = "black", span = span)
         panel.loess(plot.dat.88$Year, plot.dat.88$TL.upr,
                     lty = 3, col = "black", span = span)
         panel.loess(plot.dat.88$Year, plot.dat.88$TL.lwr,
                     lty = 3, col = "black", span = span)
         
         # Now Not Term Limits #
         panel.xyplot(plot.dat.88$Year, plot.dat.88$EstNTL,
                      lty = 2, col = "black", pch = 16)
         panel.loess(plot.dat.88$Year, plot.dat.88$EstNTL,
                     lty = 2, lwd = 3, col = "black", 
                     family = "symmetric", span = span)
         panel.loess(plot.dat.88$Year, plot.dat.88$NTL.upr,
                     lty = 3, col = "black", span = span)
         panel.loess(plot.dat.88$Year, plot.dat.88$NTL.lwr,
                     lty = 3, col = "black", span = span)
         
         # Term Limits, Post-1990 #
         panel.xyplot(plot.dat.90$Year, plot.dat.90$EstTL,
                      col = "black")
         panel.loess(plot.dat.90$Year, plot.dat.90$EstTL,
                     lty = 2, lwd = 6, col = "black", span = span)
         panel.loess(plot.dat.90$Year, plot.dat.90$TL.upr,
                     lty = 3, col = "black", span = span)
         panel.loess(plot.dat.90$Year, plot.dat.90$TL.lwr,
                     lty = 3, col = "black", span = span)
         
         # No Term Limits, Post-1990 #
         panel.xyplot(plot.dat.90$Year, plot.dat.90$EstNTL,
                      lty = 2, col = "black")
         panel.loess(plot.dat.90$Year, plot.dat.90$EstNTL,
                     lty = 2, lwd = 3, col = "black", 
                     family = "symmetric", span = span)
         panel.loess(plot.dat.90$Year, plot.dat.90$NTL.upr,
                     lty = 3, col = "black", span = span)
         panel.loess(plot.dat.90$Year, plot.dat.90$NTL.lwr,
                     lty = 3, col = "black", span = span)
         
         # Ablines for Term Limits Adopt, Imp #
         panel.abline(v = 1990, lwd = 2.5, lty = 3,
                      col = "black")
         panel.abline(v = 2000, lwd = 2.5, lty = 3,
                      col = "black")
         },
       key = list(text = list(text = c("Term Limits", 
                                       "Without Term Limits"), cex = 1.25),
                  points = list(pch = c(17, 16), col = c("black", "black"), cex = .75),
                  lines = list(lty = c(6, 3), col = c("black", "black"), cex = 1),
                  space = "top", border = T, padding.text = 2.5)
)


################################
## Formal Test of Term Limits ##
## Diff-in-Diff Analysis      ##
## x = tl, y = ntl            ##
################################

t.test(plot.dat$EstTL, plot.dat$EstNTL) # t = -2.7, meanx = 0.09, meany = 0.13 #
t.test(plot.dat.88$EstTL, plot.dat.88$EstNTL) # t = -0.77, meanx = 0.094, meany = 0.106 #
t.test(plot.dat.90$EstTL, plot.dat.90$EstNTL) # t = -3.0, meanx = 0.098, meany = 0.152 #


###########################################################
## Compare Slopes to Slopes Rather than Values to Values ##
###########################################################

lag.plot.dat <- do_lag(plot.dat, 
                         variables = c("EstTL", "EstNTL"),
                         num_periods = 1)

lag.plot.dat$diffTL <- lag.plot.dat$EstTL - lag.plot.dat$EstTL1
lag.plot.dat$diffNTL <- lag.plot.dat$EstNTL - lag.plot.dat$EstNTL1


## Compare before term limits ##

lag.plot.dat.88 <- do_lag(plot.dat.88, 
                          variables = c("EstTL", "EstNTL"),
                          num_periods = 1)

lag.plot.dat.88$diffTL <- lag.plot.dat.88$EstTL - lag.plot.dat.88$EstTL1
lag.plot.dat.88$diffNTL <- lag.plot.dat.88$EstNTL - lag.plot.dat.88$EstNTL1


## Compare after term limits ##

lag.plot.dat.90 <- do_lag(plot.dat.90, 
                       variables = c("EstTL", "EstNTL"),
                       num_periods = 1)

lag.plot.dat.90$diffTL <- lag.plot.dat.90$EstTL - lag.plot.dat.90$EstTL1
lag.plot.dat.90$diffNTL <- lag.plot.dat.90$EstNTL - lag.plot.dat.90$EstNTL1


###########################
## And t-test the slopes ##
###########################

t.test(lag.plot.dat$diffTL, lag.plot.dat$diffNTL) # t = -0.04, meanx = -0.00095, meany = 0.0006 #
t.test(lag.plot.dat.90$diffTL, lag.plot.dat.90$diffNTL) # t = 0.035, meanx = -0.0012, meany = -0.0021 #
t.test(lag.plot.dat.88$diffTL, lag.plot.dat.88$diffNTL) # t = -0.38, meanx = -0.0017, meany = 0.0077 #


##########################


################################
## Term Limits Implementation ##
## Rdest and manual estimate  ##
################################

dat.ti <- na.omit(tl.dat[which(tl.dat$termlimitsimplement == 1 
                               & tl.dat$year >= 1990),]) #5374 obs #

dat.nti <- na.omit(tl.dat[which(tl.dat$termlimitsimplement == 0 
                          & tl.dat$year >= 1990),]) # 29546 obs #


###############################################################
## Use RDEstimate to obtain RD estimates, optimal bandwidths ##
###############################################################

rd.ti <- RDestimate(votemarg ~ votelag, data = dat.ti, cutpoint = 0.5)
summary(rd.ti) # optimal bandwidth 0.368, obs 2809 # # est 0.0853 #

rd.nti <- RDestimate(votemarg ~ votelag, data = dat.nti, cutpoint = 0.5)
summary(rd.nti) # optimal bandwidth 0.1220, obs 10614 ## est 0.0751 #


#####################################
## Manual Estimation of RD effects ##
#####################################

## move to optimal bandwidth ##

dat.ti <- dat.ti[which(dat.ti$votelag >= 0.5 - rd.ti$bw[1] 
                       & dat.ti$votelag <= 0.5 + rd.ti$bw[1]),] # 2809 obs #


w <- dat.ti$wonlag
xc <- dat.ti$votelag-0.5
tl <- dat.ti$termlimitsimplement # should always = 1 #
y <- dat.ti$votemarg

## estimate ##

mt <- lm(y~w*xc)
est.mt <- mt$coef[2] # 0.0853 #
se.mt <- sqrt(diag(vcovHC(mt)))[2] # 0.00830 #

b <- seq(from = 0.001, to = 0.999, by = .0035) # generates binwidths #
mid <- seq(from = 0.003, to = 0.997, by = .0035) # generates midpoints #
count <- rep(NA,length(mid))
m <- 1

for(m in 1:length(count)) {
  sel <- which((xc+0.5) > b[m] & (xc+0.5) <= b[(m+1)])
  count[m] <- mean(y[sel]) # generates average value of y in bin #
}


###############################################
## FIGURE 6A: RD Effect, Term-Limited States ##
###############################################

par(pty = "s")
plot(mid-0.5, count, xlab = "Vote Share - 0.50 in First Election", ylab = "Vote Share in Next Election", cex.lab = 1.3, cex.axis = 1.3, pch = 19, col = "grey", main="RD Effect, Term-Limited States", sub = "", xlim=c(-rd.ti$bw[1], rd.ti$bw[1]), ylim=c(0.2,0.8))
x.plot <- seq(from = -rd.ti$bw[1], to = 0, length.out = 1000)
y.plot <- mt$coef[1] +
  mt$coef[3] * x.plot

x.plotz <- seq(from = 0, to = rd.ti$bw[1], length.out = 1000)
y.plotz <- mt$coef[1] +
  mt$coef[2] +
  mt$coef[3] * x.plotz +
  mt$coef[4] * x.plotz 

lines(x = x.plot, y = y.plot, col = "black", lwd = 4, lty = 3)
lines(x = x.plotz, y = y.plotz, col = "black", lwd = 4, lty = 3)
lines(x = c(0,0), y = c(y.plot[1000],y.plotz[1]), col = "black", lwd = 4)
text(x = -0.014, y = 0.67, bquote(widehat(tau)[RDD]^sharp == .(est.mt)~(0.008)), col = "black", cex = 1.2)


########################################
##### Without Term Limits, Same    #####
########################################


#######################
## estimate manually ##
#######################

dat.nti <- dat.nti[which(dat.nti$votelag >= 0.5 - rd.nti$bw[1] 
                         & dat.nti$votelag <= 0.5 + rd.nti$bw[1]),] # 10614 obs #


y <- dat.nti$votemarg
xc <- dat.nti$votelag-0.5
w <- dat.nti$wonlag

## estimate ##

mnt <- lm(y~w*xc, data=dat.nti)
est.nt <- mnt$coef[2] # 0.0831 #
se.nt <- sqrt(diag(vcovHC(mnt)))[2] # 0.0060 #


b <- seq(from = 0.001, to = 0.999, by = .0025) # generates binwidths #
mid <- seq(from = 0.003, to = 0.997, by = .0025) # generates midpoints #
count <- rep(NA,length(mid))
m <- 1

for(m in 1:length(count)) {
  sel <- which((xc+0.5) > b[m] & (xc+0.5) <= b[(m+1)])
  count[m] <- mean(y[sel]) # generates average value of y in bin #
}


###################################################
## FIGURE 6B: RD Effect, Non Term-Limited States ##
###################################################

plot(mid-0.5, count, xlab = "Vote Share - 0.50 in First Election", ylab = "Vote Share in Next Election", cex.lab = 1.3, cex.axis = 1.3, pch = 19, col = "grey", main="RD Effect, Non-Term-Limited States", sub = "", xlim=c(-rd.nti$bw[1], rd.nti$bw[1]), ylim=c(0.2,0.8))
x.plot <- seq(from = -rd.nti$bw[1], to = 0, length.out = 1000)
y.plot <- mnt$coef[1] +
  mnt$coef[3] * x.plot

x.plotz <- seq(from = 0, to = rd.nti$bw[1], length.out = 1000)
y.plotz <- mnt$coef[1] +
  mnt$coef[2] + 
  mnt$coef[3] * x.plotz +
  mnt$coef[4] * x.plotz

lines(x = x.plot, y = y.plot, col = "black", lwd = 4, lty = 3)
lines(x = x.plotz, y = y.plotz, col = "black", lwd = 4, lty = 3)
lines(x = c(0,0), y = c(y.plot[1000],y.plotz[1]), col = "black", lwd = 4)
text(x = -0.014, y = 0.67, bquote(widehat(tau)[RDD]^sharp == .(est.nt)~(0.006)), col = "black", cex = 1.2)


#####################################################################
## Examine RDD before 1990, compare term limits to not term limits ##
#####################################################################


################# This means estimating for states that 
## Term limits ## eventually implemented term limits
################# but estimating before 1990

## generate new pretl variable that only accounts for states that implemented term limits reform ##

tl.dat$pretlimp <- ifelse(tl.dat$pretl == 1 & tl.dat$state == 3 |
                            tl.dat$pretl == 1 & tl.dat$state == 4 |
                            tl.dat$pretl == 1 & tl.dat$state == 5 |
                            tl.dat$pretl == 1 & tl.dat$state == 6 |
                            tl.dat$pretl == 1 & tl.dat$state == 9 |
                            tl.dat$pretl == 1 & tl.dat$state == 18 |
                            tl.dat$pretl == 1 & tl.dat$state == 19 |
                            tl.dat$pretl == 1 & tl.dat$state == 22 |
                            tl.dat$pretl == 1 & tl.dat$state == 25 |
                            tl.dat$pretl == 1 & tl.dat$state == 26 |
                            tl.dat$pretl == 1 & tl.dat$state == 28 |
                            tl.dat$pretl == 1 & tl.dat$state == 35 |
                            tl.dat$pretl == 1 & tl.dat$state == 36 |
                            tl.dat$pretl == 1 & tl.dat$state == 41
                          ,1,0)


###################################
## Now generate pretlimp dataset ##
## As before, doing pre - 1990   ##
###################################

dat.ptli <- na.omit(tl.dat[which(tl.dat$pretlimp == 1 & tl.dat$year < 1990),]) # 8175 obs #
dat.pntli <- na.omit(tl.dat[which(tl.dat$pretlimp == 0 & tl.dat$year < 1990),]) # 20520 obs #


##############################
## Estimate with RDestimate ##
##############################

rd.ptli <- RDestimate(votemarg ~ votelag, data = dat.ptl, cutpoint = 0.5)
summary(rd.ptli) # bw 0.0801, obs 2891 # # est 0.0486 #

rd.pntli <- RDestimate(votemarg ~ votelag, data = dat.pntli, cutpoint = 0.5)
summary(rd.pntli) # bw 0.106 obs = 10859 est = 0.0539 #


###########################
## Now estimate manually ##
###########################

dat.ptli <- dat.ptli[which(dat.ptli$votelag >= 0.5 - rd.ptli$bw[1] 
                            & dat.ptli$votelag <= 0.5 + rd.ptli$bw[1]),] # 2214 obs ??? #

dat.pntli <- dat.pntli[which(dat.pntli$votelag >= 0.5 - rd.pntli$bw[1] 
                       & dat.pntli$votelag <= 0.5 + rd.pntli$bw[1]),] # 10859 obs #


###################################################
## Manual Estimation, Term Limits Implementation ##
## Pre-1990 subsets, states with term limits     ##
###################################################

## generate variable names ##

w <- dat.ptli$wonlag
xc <- dat.ptli$votelag-0.5
tl <- dat.ptli$termlimitsimplement # should always = 1 #
y <- dat.ptli$votemarg

## estimate ##

mt <- lm(y~w*xc)
est.mt <- mt$coef[2] # 0.0577 #
se.mt <- sqrt(diag(vcovHC(mt)))[2] # 0.0273 #

b <- seq(from = 0.001, to = 0.999, by = .0035) # generates binwidths #
mid <- seq(from = 0.003, to = 0.997, by = .0035) # generates midpoints #
count <- rep(NA,length(mid))
m <- 1

for(m in 1:length(count)) {
  sel <- which((xc+0.5) > b[m] & (xc+0.5) <= b[(m+1)])
  count[m] <- mean(y[sel]) # generates average value of y in bin #
}


###############################################
## FIGURE 7A: RD Effect, Term-Limited States ##
## Pre-1990 Term Limits Implementation       ##
###############################################

par(pty = "s")
plot(mid-0.5, count, xlab = "Vote Share - 0.50 in First Election", ylab = "Vote Share in Next Election", cex.lab = 1.3, cex.axis = 1.3, pch = 19, col = "grey", main="RD Effect, Term-Limited States (Pre-1990)", sub = "", xlim=c(-rd.ptli$bw[1], rd.ptli$bw[1]), ylim=c(0.2,0.8))
x.plot <- seq(from = -rd.ptli$bw[1], to = 0, length.out = 1000)
y.plot <- mt$coef[1] +
  mt$coef[3] * x.plot

x.plotz <- seq(from = 0, to = rd.ptli$bw[1], length.out = 1000)
y.plotz <- mt$coef[1] +
  mt$coef[2] +
  mt$coef[3] * x.plotz +
  mt$coef[4] * x.plotz 

lines(x = x.plot, y = y.plot, col = "black", lwd = 4, lty = 3)
lines(x = x.plotz, y = y.plotz, col = "black", lwd = 4, lty = 3)
lines(x = c(0,0), y = c(y.plot[1000],y.plotz[1]), col = "black", lwd = 4)
text(x = -0.014, y = 0.67, bquote(widehat(tau)[RDD]^sharp == .(est.mt)~(0.008)), col = "black", cex = 1.2)


###################################################
## Manual Estimation, Term Limits Implementation ##
## Pre-1990 subsets, states without term limits  ##
###################################################

## generate variable names ##

w <- dat.pntli$wonlag
xc <- dat.pntli$votelag-0.5
tl <- dat.pntli$termlimitsimplement # should always = 1 #
y <- dat.pntli$votemarg

## estimate ##

mt <- lm(y~w*xc)
est.mt <- mt$coef[2] # 0.0612 #
se.mt <- sqrt(diag(vcovHC(mt)))[2] # 0.0062 #

b <- seq(from = 0.001, to = 0.999, by = .0035) # generates binwidths #
mid <- seq(from = 0.003, to = 0.997, by = .0035) # generates midpoints #
count <- rep(NA,length(mid))
m <- 1

for(m in 1:length(count)) {
  sel <- which((xc+0.5) > b[m] & (xc+0.5) <= b[(m+1)])
  count[m] <- mean(y[sel]) # generates average value of y in bin #
}


###############################################
## FIGURE 7B: RD Effect, Term-Limited States ##
## Pre-1990 Not Term Limits Implementation   ##
###############################################

par(pty = "s")
plot(mid-0.5, count, xlab = "Vote Share - 0.50 in First Election", ylab = "Vote Share in Next Election", cex.lab = 1.3, cex.axis = 1.3, pch = 19, col = "grey", main="RD Effect, Non-Term-Limited States (Pre-1990)", sub = "", xlim=c(-rd.pntli$bw[1], rd.pntli$bw[1]), ylim=c(0.2,0.8))
x.plot <- seq(from = -rd.pntli$bw[1], to = 0, length.out = 1000)
y.plot <- mt$coef[1] +
  mt$coef[3] * x.plot

x.plotz <- seq(from = 0, to = rd.pntli$bw[1], length.out = 1000)
y.plotz <- mt$coef[1] +
  mt$coef[2] +
  mt$coef[3] * x.plotz +
  mt$coef[4] * x.plotz 

lines(x = x.plot, y = y.plot, col = "black", lwd = 4, lty = 3)
lines(x = x.plotz, y = y.plotz, col = "black", lwd = 4, lty = 3)
lines(x = c(0,0), y = c(y.plot[1000],y.plotz[1]), col = "black", lwd = 4)
text(x = -0.014, y = 0.67, bquote(widehat(tau)[RDD]^sharp == .(est.mt)~(0.006)), col = "black", cex = 1.2)


####################################
## Now, Create a Plot of the DiD  ##
## Use RD Estimates to Create     ##
## The Annual Incumbency Effect   ##
## For Term Limits Implementation ##
####################################

#########################################################
## First, we need to create an annual averaged measure ##
#########################################################

## Create output frame ##
dat.annual.did.i <- matrix(NA, nrow = 2010, ncol = 7)


## Generate DiD estimates, ses ##
foreach(i = c(seq(from = 1968, to = 2010, by = 2))) %do% { ## by integrating odd-numbered years into even-numbered years as a whole election cycle, I eliminate some major problems. Odd years had absurdly-high re-election rates (many at 0.999 or 1 vote share) which meant it wasn't as useful to show parallel trends. Some odd years do not have sufficient cases to run an RD ##
  
  dat.year <- tl.dat[tl.dat$year == i | tl.dat$year == i-1,] # the election cycle # 
  
  # estimate with RDestimate to obtain bandwidth (NOT ENOUGH OBS) #
  #rde.y.tl <- RDestimate(votemarg ~ votelag, data = dat.year.tl, cutpoint = 0.5)
  #rde.y.ntl <- RDestimate(votemarg ~ votelag, data = dat.year.ntl, cutpoint = 0.5)
  
  
  # gen dat states that adopt tl #
  dat.year.tl.i <- dat.year[dat.year$pretlimp == 1,] 
  
  # gen dat states that do not #
  dat.year.ntl.i <- dat.year[dat.year$pretlimp == 0,] 
  
  
  # generate covariates for rd #
  y.tl <- dat.year.tl.i$votemarg 
  xc.tl <- dat.year.tl.i$votelag - 0.5
  w.tl <- dat.year.tl.i$wonlag
  
  y.ntl <- dat.year.ntl.i$votemarg
  xc.ntl <- dat.year.ntl.i$votelag - 0.5
  w.ntl <- dat.year.ntl.i$wonlag
  
  # estimate rd #
  m.tl.y <- lm(y.tl ~ w.tl * xc.tl)
  m.ntl.y <- lm(y.ntl ~ w.ntl * xc.ntl)
  
  # save estimates and ses #
  dat.annual.did.i[i,1] <- m.tl.y$coefficients[[2]]
  dat.annual.did.i[i,2] <- sqrt(diag(vcovHC(m.tl.y)))[[2]]
  dat.annual.did.i[i,3] <- m.ntl.y$coefficients[[2]]
  dat.annual.did.i[i,4] <- sqrt(diag(vcovHC(m.ntl.y)))[[2]]
  dat.annual.did.i[i,5] <- i
  dat.annual.did.i[i,6] <- dim(dat.year.tl.i)[1]
  dat.annual.did.i[i,7] <- dim(dat.year.ntl.i)[1]
  
}


plot.dat.i <- as.data.frame(na.omit(dat.annual.did.i))
colnames(plot.dat.i) <- c("EstTLi", "SETLi", "EstNTLi", 
                        "SENTLi", "Year", "TLiObs", "NTLiObs")
xtable(plot.dat.i)

#############################################
## Generate Confidence Intervals, plot.dat ##
#############################################

plot.dat.i$TLi.upr <- plot.dat.i$EstTLi + (1.96 * (plot.dat.i$SETLi/sqrt(22)))
plot.dat.i$TLi.lwr <- plot.dat.i$EstTLi - (1.96 * (plot.dat.i$SETLi/sqrt(22)))

plot.dat.i$NTLi.upr <- plot.dat.i$EstNTLi + (1.96 * (plot.dat.i$SENTLi/sqrt(22)))
plot.dat.i$NTLi.lwr <- plot.dat.i$EstNTLi - (1.96 * (plot.dat.i$SENTLi/sqrt(22)))

plot.dat.i <- plot.dat.i[which(plot.dat.i$Year >= 1970),] # Remove 1967-1968 where inc effect was -0.18 #


###############
## DiD Plots ##
###############
span = 0.43

xyplot(EstTLi ~ Year, data = plot.dat.i,
       aspect = 1,
       ylim = c(-0.05, 0.23),
       ylab = "Incumbency Effect",
       panel = function(x, y){
         # Term Limited RD Estimates #
         panel.xyplot(plot.dat.i$Year, plot.dat.i$EstTLi,
                      col = "black", pch = 17)
         panel.loess(plot.dat.i$Year, plot.dat.i$EstTLi,
                     lty = 6, lwd = 4, col = "black", span = span)
         # Confidence Intervals #
         panel.loess(plot.dat.i$Year, plot.dat.i$TLi.upr,
                     lty = 3, col = "black", span = span)
         panel.loess(plot.dat.i$Year, plot.dat.i$TLi.lwr,
                     lty = 3, col = "black", span = span)
         # Not-Term Limited RD Estimates #
         panel.xyplot(plot.dat.i$Year, plot.dat.i$EstNTLi,
                      lty = 3, col = "black", pch = 16)
         panel.loess(plot.dat.i$Year, plot.dat.i$EstNTLi,
                     lty = 3, lwd = 4, col = "black", 
                     family = "symmetric", span = span)
         # Confidence Intervals #
         panel.loess(plot.dat.i$Year, plot.dat.i$NTLi.upr,
                     lty = 3, col = "black", span = span)
         panel.loess(plot.dat.i$Year, plot.dat.i$NTLi.lwr,
                     lty = 3, col = "black", span = span)
         # Ablines for Critical Years #
         panel.abline(v = 1984, lwd = 2.5, lty = 3,
                      col = "black")
         panel.abline(v = 1990, lwd = 2.5, lty = 3,
                      col = "black")
         panel.abline(v = 2000, lwd = 2.5, lty = 3,
                      col = "black")
       },
       key = list(text = list(text = c("Term Limits", 
                                       "Without Term Limits"), cex = 1.25),
                  points = list(pch = c(17, 18), col = c("black", "black"), cex = .75),
                  lines = list(lty = c(6, 3), col = c("black", "black"), cex = 1),
                  space = "top", border = T, padding.text = 2.5)
) # histogram that plots all even years # # span really matters #


#############################
## Let's compare 1968-1990 ##
## versus 1990-2010        ##
#############################

plot.dati.88 <- plot.dat.i[plot.dat.i$Year <= 1988,]
plot.dati.90 <- plot.dat.i[plot.dat.i$Year >= 1990,]


## Plot Subsets, Separate Slopes ##

xyplot(EstTLi ~ Year, data = plot.dat.i,
       aspect = 1,
       ylim = c(-0.05, 0.23),
       panel = function(x, y){
         
         # Term Limits, Pre-1990 #
         panel.xyplot(plot.dati.88$Year, plot.dati.88$EstTLi,
                      col = "black", pch = 17)
         panel.loess(plot.dati.88$Year, plot.dati.88$EstTLi,
                     lty = 6, lwd = 3, col = "black", span = span)
         panel.loess(plot.dati.88$Year, plot.dati.88$TLi.upr,
                     lty = 3, col = "black", span = span)
         panel.loess(plot.dati.88$Year, plot.dati.88$TLi.lwr,
                     lty = 3, col = "black", span = span)
         
         # Now Not Term Limits #
         panel.xyplot(plot.dati.88$Year, plot.dati.88$EstNTLi,
                      lty = 3, col = "black", pch = 16)
         panel.loess(plot.dati.88$Year, plot.dati.88$EstNTLi,
                     lty = 3, lwd = 3, col = "black", 
                     family = "symmetric", span = span)
         panel.loess(plot.dati.88$Year, plot.dati.88$NTLi.upr,
                     lty = 3, col = "black", span = span)
         panel.loess(plot.dati.88$Year, plot.dati.88$NTLi.lwr,
                     lty = 3, col = "black", span = span)
         
         # Term Limits, Post-1990 #
         panel.xyplot(plot.dati.90$Year, plot.dati.90$EstTLi,
                      col = "black", pch = 17)
         panel.loess(plot.dati.90$Year, plot.dati.90$EstTLi,
                     lty = 6, lwd = 3, col = "black", span = span)
         panel.loess(plot.dati.90$Year, plot.dati.90$TLi.upr,
                     lty = 3, col = "black", span = span)
         panel.loess(plot.dati.90$Year, plot.dati.90$TLi.lwr,
                     lty = 3, col = "black", span = span)
         
         # No Term Limits, Post-1990 #
         panel.xyplot(plot.dati.90$Year, plot.dati.90$EstNTLi,
                      lty = 2, col = "black", pch = 16)
         panel.loess(plot.dati.90$Year, plot.dati.90$EstNTLi,
                     lty = 3, lwd = 3, col = "black", 
                     family = "symmetric", span = span)
         panel.loess(plot.dati.90$Year, plot.dati.90$NTLi.upr,
                     lty = 3, col = "black", span = span)
         panel.loess(plot.dati.90$Year, plot.dati.90$NTLi.lwr,
                     lty = 3, col = "black", span = span)
         
         # Ablines for Term Limits Adopt, Imp #
         panel.abline(v = 1990, lwd = 2.5, lty = 3,
                      col = "black")
         panel.abline(v = 2000, lwd = 2.5, lty = 3,
                      col = "black")
       },
       key = list(text = list(text = c("Term Limits", 
                                       "Without Term Limits"), cex = 1.25),
                  points = list(pch = c(17, 18), col = c("black", "black"), cex = .75),
                  lines = list(lty = c(6, 3), col = c("black", "black"), cex = 1),
                  space = "top", border = T, padding.text = 2.5)
)


################################
## Formal Test of Term Limits ##
## Diff-in-Diff Analysis      ##
## x = tli, y = ntli          ##
################################

t.test(plot.dat.i$EstTLi, plot.dat.i$EstNTLi) # t = -1.6, meanx = 0.09905, meany = 0.12073 #
t.test(plot.dati.88$EstTLi, plot.dati.88$EstNTLi) # t -0.43, meanx 0.098, meany 0.1047 #
t.test(plot.dati.90$EstTLi, plot.dati.90$EstNTLi) # t -3.6, meanx 0.098, meany 0.1047 #

###########################################################
## Compare Slopes to Slopes Rather than Values to Values ##
###########################################################

lag.plot.dat.i <- do_lag(plot.dat.i, 
                       variables = c("EstTLi", "EstNTLi"),
                       num_periods = 1)

lag.plot.dat.i$diffTLi <- lag.plot.dat.i$EstTLi - lag.plot.dat.i$EstTLi1
lag.plot.dat.i$diffNTLi <- lag.plot.dat.i$EstNTLi - lag.plot.dat.i$EstNTLi1


## Compare before term limits ##

lag.plot.dat.i.88 <- do_lag(plot.dati.88, 
                          variables = c("EstTLi", "EstNTLi"),
                          num_periods = 1)

lag.plot.dat.i.88$diffTLi <- lag.plot.dat.i.88$EstTLi - lag.plot.dat.i.88$EstTLi1
lag.plot.dat.i.88$diffNTLi <- lag.plot.dat.i.88$EstNTLi - lag.plot.dat.i.88$EstNTLi1


## Compare after term limits ##

lag.plot.dat.i.90 <- do_lag(plot.dati.90, 
                          variables = c("EstTLi", "EstNTLi"),
                          num_periods = 1)

lag.plot.dat.i.90$diffTLi <- lag.plot.dat.i.90$EstTLi - lag.plot.dat.i.90$EstTLi1
lag.plot.dat.i.90$diffNTLi <- lag.plot.dat.i.90$EstNTLi - lag.plot.dat.i.90$EstNTLi1


###########################
## And t-test the slopes ##

t.test(lag.plot.dat.i$diffTLi, lag.plot.dat.i$diffNTLi) # t -0.083, meanx  -0.036, meany 0.0004 #
t.test(lag.plot.dat.i.90$diffTLi, lag.plot.dat.i.90$diffNTLi) # t 0.1, meanx -0.056, meany -0.0027 #
t.test(lag.plot.dat.i.88$diffTLi, lag.plot.dat.i.88$diffNTLi) # t -0.27, meanx -0.0003, meany 0.006 #

################################################
## Comparison of the reform, before and after ##
## Using RDestimate technique, not manual     ##
################################################

rd.ti$est[1] - rd.nti$est[1] # compares term limits to not term limits, post-1990 #

rd.ptli$est[1] - rd.pntli$est[1] # compares prospective term-limits to prospective not, pre-1990 #

rd.ti$est[1] - rd.ptli$est[1] # compares term limits before and after #

rd.nti$est[1] - rd.pntli$est[1] # compares not term limits before and after #


#############################################
## Compare RDestimate to Manual Estimation ##
#############################################

rd.ti$est[1] - est.mt[1] # term limits, post-1990 # # 0.0207 #

rd.ptli$est[1] - est.pt[1] # term limits, pre-1990 # # -0.00431 #

rd.nti$est[1] - est.nt[1] # not term limits, post-1990 # # -0.00446 #

rd.pntli$est[1] - est.pnt[1] # not term limits, pre-1990 # # -0.0102 #


##########################
##########################


##########################
## Legislative Staffing ##
##########################

########################################
### Staffing Increases and Decreases ###
########################################

#################################
## Generate Staff Size Dataset ##
## Remove NAs for term limits  ##
#################################

ss.dat <- na.omit(dat1[,c("caseid", "votelag", "votemarg", "wonlag",
                          "pre90", "year", "totvotes",
                          "incumbent", "state", "district",
                          "chambersize", "statpop", "staffstep",
                          "stafflinear", "staffpop",
                          "staffdiff")]) # 44240 obs #

dim(ss.dat[which(ss.dat$staffdiff >= 1 | ss.dat$staffdiff <= -1),])

#################################################### Zero will be considered
## Now estimate positive changes to staffing size ## A positive number for
#################################################### These analyses

dat.p <- na.omit(ss.dat[which(ss.dat$staffdiff >= 0),]) # generates 22186 observations #
dat.n <- na.omit(ss.dat[which(ss.dat$staffdiff < 0),]) # generates 22054 obs #


##############################
## Estimate with RDestimate ##
##############################

rd.ps <- RDestimate(votemarg ~ votelag, data = dat.p, cutpoint = 0.5)
summary(rd.ps) # bw 0.2220, obs = 13276, est = 0.0848 #

rd.ns <- RDestimate(votemarg ~ votelag, data = dat.n, cutpoint = 0.5)
summary(rd.ns) # bw 0.0823, obs = 5526, est = 0.0735 #


################################################
## Now Manually Estimate Staff Size Increases ##
################################################


########################
## generate variables ##
########################

dat.p <- dat.p[which(dat.p$votelag >= 0.5 - rd.ps$bw[1] 
                     & dat.p$votelag <= 0.5 + rd.ps$bw[1]),] # 13276 obs #

y <- dat.p$votemarg
xc <- dat.p$votelag - 0.5
w <- dat.p$wonlag

ss.p <- lm(y ~ w * xc)
est.ss.p <- ss.p$coef[2]
se.ss.p <- sqrt(diag(vcovHC(ss.p)))[2]


b <- seq(from = 0.001, to = 0.999, by = .0035) # generates binwidths #
mid <- seq(from = 0.003, to = 0.997, by = .0035) # generates midpoints #
count <- rep(NA,length(mid))
m <- 1

for(m in 1:length(count)) {
  sel <- which((xc+0.5) > b[m] & (xc+0.5) <= b[(m+1)])
  count[m] <- mean(na.omit(y[sel])) # generates average value of y in bin #
}

############################################
## FIGURE 8A: STAFF GROWTH AND INCUMBENCY ##
############################################

par(pty = "s")
plot(mid-0.5, count, xlab = "Vote Share - 0.50 in First Election", ylab = "Vote Share in Next Election", cex.lab = 1.3, cex.axis = 1.3, pch = 19, col = "grey", main="RD Effect, Legislative Staffing Increases", xlim=c(-rd.ps$bw[1], rd.ps$bw[1]), ylim=c(0.2,0.8))
x.plot <- seq(from = -rd.ps$bw[1], to = 0, length.out = 1000)
y.plot <- ss.p$coef[1] +
  ss.p$coef[3] * x.plot

x.plotz <- seq(from = 0, to = rd.ps$bw[1], length.out = 1000)
y.plotz <- ss.p$coef[1] +
  ss.p$coef[2] +
  ss.p$coef[3] * x.plotz +
  ss.p$coef[4] * x.plotz

lines(x = x.plot, y = y.plot, col = "black", lwd = 4, lty = 3)
lines(x = x.plotz, y = y.plotz, col = "black", lwd = 4, lty = 3)
lines(x = c(0,0), y = c(y.plot[1000],y.plotz[1]), col = "black", lwd = 4)
text(x = -0.014, y = 0.67, bquote(widehat(tau)[RDD]^sharp == .(est.ss.p)~(0.005)), col = "black", cex = 1.2)



################################################
## Now Manually Estimate Staff Size Increases ##
################################################


########################
## generate variables ##
########################

dat.n <- dat.n[which(dat.n$votelag >= 0.5 - rd.ns$bw[1] 
               & dat.n$votelag <= 0.5 + rd.ns$bw[1]),] # 5526 obs #


y <- dat.n$votemarg
xc <- dat.n$votelag - 0.5
w <- dat.n$wonlag

ss.n <- lm(y ~ w * xc)
est.ss.n <- ss.n$coef[2]
se.ss.n <- sqrt(diag(vcovHC(ss.n)))[2]

b <- seq(from = 0.001, to = 0.999, by = .0035) # generates binwidths #
mid <- seq(from = 0.003, to = 0.997, by = .0035) # generates midpoints #
count <- rep(NA,length(mid))
m <- 1

for(m in 1:length(count)) {
  sel <- which((xc+0.5) > b[m] & (xc+0.5) <= b[(m+1)])
  count[m] <- mean(y[sel]) # generates average value of y in bin #
}


############################################
## FIGURE 8B: STAFF CUTS AND INCUMBENCY   ##
############################################

par(pty = "s")
plot(mid-0.5, count, xlab = "Vote Share - 0.50 in First Election", ylab = "Vote Share in Next Election", cex.lab = 1.3, cex.axis = 1.3, pch = 19, col = "grey", main="RD Effect, Legislative Staffing Decreases", xlim=c(-rd.ns$bw[1], rd.ns$bw[1]), ylim=c(0.2,0.8))
x.plot <- seq(from = -rd.ns$bw[1], to = 0, length.out = 1000)
y.plot <- ss.n$coef[1] +
  ss.n$coef[3] * x.plot

x.plotz <- seq(from = 0, to = rd.ns$bw[1], length.out = 1000)
y.plotz <- ss.n$coef[1] +
  ss.n$coef[2] +
  ss.n$coef[3] * x.plotz +
  ss.n$coef[4] * x.plotz

lines(x = x.plot, y = y.plot, col = "black", lwd = 4, lty = 3)
lines(x = x.plotz, y = y.plotz, col = "black", lwd = 4, lty = 3)
lines(x = c(0,0), y = c(y.plot[1000],y.plotz[1]), col = "black", lwd = 4)
text(x = -0.014, y = 0.67, bquote(widehat(tau)[RDD]^sharp == .(est.ss.n)~(0.008)), col = "black", cex = 1.2)


#######################
## Staffing Size DiD ##
#######################

#########################################################
## First, we need to create an annual averaged measure ##
#########################################################

## Create output frame ##
dat.annual.ss <- matrix(NA, nrow = 2008, ncol = 7)

ss.dat$staffinc <- ifelse(ss.dat$staffdiff >= 0, 1, 0)

## Generate DiD estimates, ses ##
foreach(i = c(seq(from = 1980, to = 2008, by = 2))) %do% { ## by integrating odd-numbered years into even-numbered years as a whole election cycle, I eliminate some major problems. Odd years had absurdly-high re-election rates (many at 0.999 or 1 vote share) which meant it wasn't as useful to show parallel trends. Some odd years do not have sufficient cases to run an RD ##
  
  tmp <- ss.dat[which(ss.dat$year == i | ss.dat$year == i-1),] # the election cycle # 

  
  # gen dat states that adopt tl #
  dat.year.sp <- tmp[which(tmp$year == i & tmp$staffinc == 1),] 
  
  # gen dat states that do not #
  dat.year.sn <- tmp[which(tmp$year == i & tmp$staffinc == 0),] 
  
  
  # generate covariates for rd #
  y.sp <- dat.year.sp$votemarg 
  xc.sp <- dat.year.sp$votelag - 0.5
  w.sp <- dat.year.sp$wonlag
  
  y.sn <- dat.year.sn$votemarg
  xc.sn <- dat.year.sn$votelag - 0.5
  w.sn <- dat.year.sn$wonlag
  
  # estimate rd #
  m.sp <- lm(y.sp ~ w.sp * xc.sp)
  m.sn <- lm(y.sn ~ w.sn * xc.sn)
  
  # save estimates and ses #
  dat.annual.ss[i,1] <- m.sp$coefficients[[2]]
  dat.annual.ss[i,2] <- sqrt(diag(vcovHC(m.sp)))[[2]]
  dat.annual.ss[i,3] <- m.sn$coefficients[[2]]
  dat.annual.ss[i,4] <- sqrt(diag(vcovHC(m.sn)))[[2]]
  dat.annual.ss[i,5] <- i
  dat.annual.ss[i,6] <- dim(dat.year.sp)[1]
  dat.annual.ss[i,7] <- dim(dat.year.sn)[1]
  
}


plot.dat.ss <- as.data.frame(na.omit(dat.annual.ss))
colnames(plot.dat.ss) <- c("EstSP", "SESP", "EstSN", 
                           "SESN", "Year", "SPObs", "SNObs")
xtable(plot.dat.ss)

#############################################
## Generate Confidence Intervals, plot.dat ##
#############################################

plot.dat.ss$SP.upr <- plot.dat.ss$EstSP + (1.96 * (plot.dat.ss$SESP/sqrt(11)))
plot.dat.ss$SP.lwr <- plot.dat.ss$EstSP - (1.96 * (plot.dat.ss$SESP/sqrt(11)))

plot.dat.ss$SN.upr <- plot.dat.ss$EstSN + (1.96 * (plot.dat.ss$SESN/sqrt(11)))
plot.dat.ss$SN.lwr <- plot.dat.ss$EstSN - (1.96 * (plot.dat.ss$SESN/sqrt(11)))

plot.dat.ss <- plot.dat.ss[which(plot.dat.ss$Year >= 1970),] # Remove 1967-1968 where inc effect was -0.18 #


###############
## DiD Plots ##
###############
span = 0.9

xyplot(EstSP ~ Year, data = plot.dat.ss,
       aspect = 1,
       ylim = c(-0.05, 0.23),
       ylab = "Incumbency Effect",
       panel = function(x, y){
         # Term Limited RD Estimates #
         panel.xyplot(plot.dat.ss$Year, plot.dat.ss$EstSP,
                      col = "black", pch = 17)
         panel.loess(plot.dat.ss$Year, plot.dat.ss$EstSP,
                     lty = 6, lwd = 4, col = "black", span = span)
         # Confidence Intervals #
         panel.loess(plot.dat.ss$Year, plot.dat.ss$SP.upr,
                     lty = 3, col = "black", span = span)
         panel.loess(plot.dat.ss$Year, plot.dat.ss$SP.lwr,
                     lty = 3, col = "black", span = span)
         # Not-Term Limited RD Estimates #
         panel.xyplot(plot.dat.ss$Year, plot.dat.ss$EstSN,
                      lty = 3, col = "black", pch = 16)
         panel.loess(plot.dat.ss$Year, plot.dat.ss$EstSN,
                     lty = 3, lwd = 4, col = "black", 
                     family = "symmetric", span = span)
         # Confidence Intervals #
         panel.loess(plot.dat.ss$Year, plot.dat.ss$SN.upr,
                     lty = 3, col = "black", span = span)
         panel.loess(plot.dat.ss$Year, plot.dat.ss$SN.lwr,
                     lty = 3, col = "black", span = span)
         # Ablines for Critical Years #
         panel.abline(v = 1984, lwd = 2.5, lty = 3,
                      col = "black")
         panel.abline(v = 1990, lwd = 2.5, lty = 3,
                      col = "black")
         panel.abline(v = 2000, lwd = 2.5, lty = 3,
                      col = "black")
       },
       key = list(text = list(text = c("Staffing Increases", 
                                       "Staffing Decreases"), cex = 1.25),
                  points = list(pch = c(17, 16), col = c("black", "black"), cex = .75),
                  lines = list(lty = c(6, 3), col = c("black", "black"), cex = 1),
                  space = "top", border = T, padding.text = 2.5)
) # histogram that plots all even years # # span really matters #


#############################
## Let's compare 1968-1990 ##
## versus 1990-2010        ##
#############################

plot.datss.88 <- plot.dat.ss[plot.dat.ss$Year <= 1988,]
plot.datss.90 <- plot.dat.ss[plot.dat.ss$Year >= 1990,]


## Plot Subsets, Separate Slopes ##
span = 1.2

xyplot(EstSP ~ Year, data = plot.dat.ss,
       aspect = 1,
       ylim = c(-0.05, 0.23),
       ylab = "Incumbency Effect",
       panel = function(x, y){
         
         # Term Limits, Pre-1990 #
         panel.xyplot(plot.datss.88$Year, plot.datss.88$EstSP,
                      col = "black", pch = 17)
         panel.loess(plot.datss.88$Year, plot.datss.88$EstSP,
                     lty = 6, lwd = 3, col = "black", span = span)
         panel.loess(plot.datss.88$Year, plot.datss.88$SP.upr,
                     lty = 3, col = "black", span = span)
         panel.loess(plot.datss.88$Year, plot.datss.88$SP.lwr,
                     lty = 3, col = "black", span = span)
         
         # Now Not Term Limits #
         panel.xyplot(plot.datss.88$Year, plot.datss.88$EstSN,
                      lty = 2, col = "black", pch = 16)
         panel.loess(plot.datss.88$Year, plot.datss.88$EstSN,
                     lty = 3, lwd = 3, col = "black", 
                     family = "symmetric", span = span)
         panel.loess(plot.datss.88$Year, plot.datss.88$SN.upr,
                     lty = 3, col = "black", span = span)
         panel.loess(plot.datss.88$Year, plot.datss.88$SN.lwr,
                     lty = 3, col = "black", span = span)
         
         # Term Limits, Post-1990 #
         panel.xyplot(plot.datss.90$Year, plot.datss.90$EstSP,
                      col = "black", pch = 17)
         panel.loess(plot.datss.90$Year, plot.datss.90$EstSP,
                     lty = 6, lwd = 3, col = "black", span = span)
         panel.loess(plot.datss.90$Year, plot.datss.90$SP.upr,
                     lty = 3, col = "black", span = span)
         panel.loess(plot.datss.90$Year, plot.datss.90$SP.lwr,
                     lty = 3, col = "black", span = span)
         
         # No Term Limits, Post-1990 #
         panel.xyplot(plot.datss.90$Year, plot.datss.90$EstSN,
                      lty = 2, col = "black", pch = 16)
         panel.loess(plot.datss.90$Year, plot.datss.90$EstSN,
                     lty = 3, lwd = 3, col = "black", 
                     family = "symmetric", span = span)
         panel.loess(plot.datss.90$Year, plot.datss.90$SN.upr,
                     lty = 3, col = "black", span = span)
         panel.loess(plot.datss.90$Year, plot.datss.90$SN.lwr,
                     lty = 3, col = "black", span = span)
         
         # Ablines for Term Limits Adopt, Imp #
         panel.abline(v = 1990, lwd = 2.5, lty = 3,
                      col = "black")
         panel.abline(v = 2000, lwd = 2.5, lty = 3,
                      col = "black")
       },
       key = list(text = list(text = c("Staffing Increases", 
                                       "Staffing Decreases"), cex = 1.25),
                  points = list(pch = c(17, 18), col = c("black", "black"), cex = .75),
                  lines = list(lty = c(6, 3), col = c("black", "black"), cex = 1),
                  space = "top", border = T, padding.text = 2.5)
)


#################################
## Formal test of Diff-in-Diff ##
#################################

t.test(plot.dat.ss$EstSP, plot.dat.ss$EstSN) # t = -1.7, meanx = 0.1252, meany = 0.1451 #


########################################
## Compare Slopes of Staffing Changes ##
########################################

lag.ss <- do_lag(plot.dat.ss, variables = c("EstSP", "EstSN"),
                 num_periods = 1)

lag.ss$diffSP <- lag.ss$EstSP - lag.ss$EstSP1
lag.ss$diffSN <- lag.ss$EstSN - lag.ss$EstSN1


######################
## T-Test of Slopes ##
######################

t.test(lag.ss$diffSP, lag.ss$diffSN) # t = 0.32, meanx = 0.007, meany = 0.002 #

############################################


#######################################################
############### BEGIN MAPPING #########################
#######################################################


###############################
## Term Limits - Map Version ##
###############################

## first, set up data for appropriate format ##

state.names <- map(database = "state")$names ## create vector of state names ##
state.tl <- as.matrix(rep(1, 63)) ## create vector of state term limits ##
state.tl[c(2, 3, 4, 5, 9, 17, 18, 23:24, 27, 28, 29, 30, 42, 43, 48),] <- 2 ## create states who adopt term limits ##
state.tl[c(11, 20:22, 44, 51, 56:60, 63),] <- 3 ## add in states who adopt/repeal ##

states <- as.data.frame(cbind(state.names, state.tl)) # merge together #
states$V2 <- as.numeric(states$V2)

#################################
## Now let's try making a map! ##
#################################

colors = brewer.pal(4,"Greys")
states$colorBuckets <- as.numeric(cut(states$V2, c(0, 1, 2, 3)))

leg.txt <- c("No Term Limits", "Term Limits", "Term Limits Repealed")

data(state.fips)
cnty.fips <- state.fips$polyname[match(map("state", plot=FALSE)$names,state.fips$polyname)]
colorsmatched <- states$colorBuckets [match(cnty.fips, states$state.names)]


#############################
####### Plot the Map ########
#############################

map <- map(database = "state", 
           boundary = T,
           interior = T,
           fill = T, 
           resolution = 0, 
           lty = 1, 
           projection = "polyconic",
           col = colors[colorsmatched]
)
#map("state", col = "white", fill = FALSE, add = TRUE, lty = 1, lwd = 0.2,projection="polyconic")

legend("bottomright", leg.txt, fill = colors, cex = 0.45)


#####################
## GGPLOT2 Version ##
#####################

# https://jabranham.com/blog/2016/03/ggplot-maps/ #

geompoly <- data("fifty_states")
dat.map <- data.frame(state = tolower(rownames(USArrests)), USArrests)
dat.map$tls <- c(0, 0, 1, 1, 1, 1, 0, 0, 1, 0, 0, 2,
               0, 0, 0, 0, 0, 1, 1, 0, 2, 1, 0, 0, 
               1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 1, 1,
               2, 0, 0, 0, 1, 0, 0, 2, 0, 0, 2, 0,
               0, 2)
geomdat <- data.frame(fifty_states)

mapdat <- merge(geomdat, dat.map, by.x = "id", by.y = "state", all.x = T)
mapdat <- mapdat[order(mapdat$order),]

################
## Now plot!  ##
################

map.out <- ggplot(mapdat, aes(map_id = id)) +
  geom_map(aes(fill = tls), map = fifty_states) +
  expand_limits(x = fifty_states$long, y = fifty_states$lat) +
  coord_map() +
  scale_x_continuous(breaks = NULL) + 
  scale_y_continuous(breaks = NULL) +
  labs(x = "", y = "") +
  expand_limits(x = fifty_states$long, y = fifty_states$lat) +
  geom_polygon(aes(group = group, x = long, y = lat), fill = NA, color = "black") + 
  theme(legend.position = "none", 
        panel.background = element_blank()) +
  scale_fill_gradient2(name = "tls", midpoint = 1,
                       low = "#FFFFFF", mid = "#333333", high = "#999999")
 # remove scale at bottom, fiddle with colors #
  

######################################
## Create Map for Staffing Cuts Now ##
######################################

ss.79 <- statyr[which(statyr$year == 1979),]
ss.88 <- statyr[which(statyr$year == 1988),]
ss.96 <- statyr[which(statyr$year == 1996),] 
ss.03 <- statyr[which(statyr$year == 2003),]

ss.79$ staffpop <- ss.79$staffsize/ss.79$populationofstate
ss.88$ staffpop <- ss.88$staffsize/ss.88$populationofstate
ss.96$ staffpop <- ss.96$staffsize/ss.96$populationofstate
ss.03$ staffpop <- ss.03$staffsize/ss.03$populationofstate

tmp.s1 <- aggregate(ss.79$staffpop, list(Region = ss.79$state), mean)
tmp.s2 <- aggregate(ss.88$staffpop, list(Region = ss.88$state), mean)

tmp.s3 <- merge(tmp.s1, tmp.s2, by.x = "Region", by.y = "Region")
colnames(tmp.s3) <- c("statename", "in1979", "in1988")

# and after reforms were implemented #
tmp.s4 <- aggregate(ss.88$staffpop, list(Region = ss.88$state), mean)
tmp.s5 <- aggregate(ss.96$staffpop, list(Region = ss.96$state), mean)

tmp.s6 <- merge(tmp.s4, tmp.s5, by.x = "Region", by.y = "Region")
colnames(tmp.s6) <- c("statename", "in1988", "in1996")

####################################
### Difference From pre to post  ###
####################################

tmp.s3$diff <- (tmp.s3$in1988 - tmp.s3$in1979) * 100000
tmp.s6$diff <- (tmp.s6$in1996 - tmp.s6$in1988) * 100000

####################################
## Create Database of State Names ##
## And Insert Staff Differences   ##
## For Pre and Post Reforms       ##
####################################

tmp.all <- as.data.frame(cbind(tmp.s3$statename, tmp.s3$diff, tmp.s6$diff))
colnames(tmp.all) <- c("state", "diff1", "diff2")

diff1.n <- c(tmp.all$diff1[1:26], 0, tmp.all$diff1[27:49])
diff2.n <- c(tmp.all$diff2[1:26], 0, tmp.all$diff2[27:49])

diff1.c <- cut(diff1.n, breaks = c(-Inf, -5, -0.01, 0.01, 5, Inf),
               labels = c("> -5 Cut", "0-5 Cut", "No Cut", "0-5 Growth", "> 5 Growth"))

diff2.c <- cut(diff2.n, breaks = c(-Inf, -5, -0.01, 0.01, 5, Inf),
               labels = c("> -5 Cut", "0-5 Cut", "No Cut", "0-5 Growth", "> 5 Growth"))

map.ss <- as.data.frame(cbind(diff1.c, diff2.c))
colnames(map.ss) <- c("diff7988", "diff9688")
map.ss$state <- dat.map$state

mapdat2 <- merge(geomdat, map.ss, by.x = "id", by.y = "state", all.x = T)
mapdat2 <- mapdat2[order(mapdat2$order),]


## And GGPlot! ##

map.ss1 <- ggplot(mapdat2, aes(map_id = id)) +
  geom_map(aes(fill = diff7988), map = fifty_states) +
  expand_limits(x = fifty_states$long, y = fifty_states$lat) +
  coord_map() +
  scale_x_continuous(breaks = NULL) + 
  scale_y_continuous(breaks = NULL) +
  labs(x = "", y = "") +
  expand_limits(x = fifty_states$long, y = fifty_states$lat) +
  geom_polygon(aes(group = group, x = long, y = lat), fill = NA, color = "black",
               plot.legend = F) + 
  theme(legend.position = "bottom", 
        panel.background = element_blank()) +
  scale_fill_gradient2(name = "diff7988", midpoint = 3,
                       low = "#4d4d4d", mid = "#BABABA", high = "#FFFFFF")


map.ss2 <- ggplot(mapdat2, aes(map_id = id)) +
  geom_map(aes(fill = diff9688), map = fifty_states) +
  expand_limits(x = fifty_states$long, y = fifty_states$lat) +
  coord_map() +
  scale_x_continuous(breaks = NULL) + 
  scale_y_continuous(breaks = NULL) +
  labs(x = "", y = "") +
  expand_limits(x = fifty_states$long, y = fifty_states$lat) +
  geom_polygon(aes(group = group, x = long, y = lat), fill = NA, color = "black") + 
  theme(legend.position = "bottom", 
        panel.background = element_blank()) +
  scale_fill_gradient2(name = "diff9688", midpoint = 3,
                       low = "#4d4d4d", mid = "#BABABA", high = "#FFFFFF")


#######################
## Print All GGPlots ##
#######################

map.out
map.ss1
map.ss2
 
 
##### Implications for Party Intervention #####

################## Only elections where
## Senior Slump ## incumbency = 0 & inclag = 1
################## to test for senior slump

dat.inc <- dat1[which(dat1$incumbent == 0 & dat1$inclag == 1),] # 10198 #

dat.inc.90 <- dat.inc[which(dat.inc$year >= 1990),] # 5582 #
dat.inc.90.tl <- dat.inc.90[which(dat.inc.90$termlimitsadopt == 1),] # 3483 #
dat.inc.90.ntl <- dat.inc.90[which(dat.inc.90$termlimitsadopt == 0),] # 2099 #


dat.inc.88 <- dat.inc[which(dat.inc$year <= 1988),] # 4608 #
dat.inc.88.tl <- dat.inc.88[which(dat.inc.88$pretl == 1),] # 1860 #
dat.inc.88.ntl <- dat.inc.88[which(dat.inc.88$pretl == 0),] # 2748 #


## generate rd variables and test ##

rd.tl.inc.90 <- RDestimate(votemarg ~ votelag, data = dat.inc.90.tl, cutpoint = 0.5)
summary(rd.tl.inc.90) # bw 0.1353, obs 646, est 0.0653 #
rd.ntl.inc.90 <- RDestimate(votemarg ~ votelag, data = dat.inc.90.ntl, cutpoint = 0.5)
summary(rd.ntl.inc.90) # bw 0.1792, obs 1569, est 0.0421 #


rd.tl.inc.88 <- RDestimate(votemarg ~ votelag, data = dat.inc.88.tl, cutpoint = 0.5)
summary(rd.tl.inc.88) # bw 0.1298, obs 620, est 0.0038 #
rd.ntl.inc.88 <- RDestimate(votemarg ~ votelag, data = dat.inc.88.ntl, cutpoint = 0.5)
summary(rd.ntl.inc.88) # bw 0.1354, obs 1118, est 0.0432 #

####################
## staff size now ##
## senior slump   ##
####################

## generate datasets for positive and negative staff changes ##

dat.inc.90.ps <- dat.inc.90[which(dat.inc.90$staffdiff >= 0),] # 2194 #
dat.inc.90.ns <- dat.inc.90[which(dat.inc.90$staffdiff < 0),] # 2908 #

dat.inc.88.ps <- dat.inc.88[which(dat.inc.88$staffdiff >= 0),] # 1319 #
dat.inc.88.ns <- dat.inc.88[which(dat.inc.88$staffdiff < 0),] # 591 #

## and estimate ##

rd.ps.inc.90 <- RDestimate(votemarg ~ votelag, data = dat.inc.90.ps, cutpoint = 0.5)
summary(rd.ps.inc.90) # bw 0.1429, obs 805, est 0.0391 #
rd.ns.inc.90 <- RDestimate(votemarg ~ votelag, data = dat.inc.90.ns, cutpoint = 0.5)
summary(rd.ns.inc.90) # bw 0.1423, obs = 1100, est 0.0481 #

rd.ps.inc.88 <- RDestimate(votemarg ~ votelag, data = dat.inc.88.ps, cutpoint = 0.5)
summary(rd.ps.inc.88) # bw 0.1593, obs 570, est -0.0020 #
rd.ns.inc.88 <- RDestimate(votemarg ~ votelag, data = dat.inc.88.ns, cutpoint = 0.5)
summary(rd.ns.inc.88) # bw 0.1229, obs 190, est 0.0932 #

#############################
## Estimates, SEs, and Obs ##
## Into APPENDIX Table 2   ##
#############################


##### Campaign Contributions Party Intervention #####

contributions.candid <- (accesscont.dat$CandId * 10000) + accesscont.dat$year
contributions.totals <- vector()

for(i in 1:dim(accesscont.dat)[1]){
  
  contributions.totals[i] <- sum(accesscont.dat[i,c(15:102)])
  
}

contributions.dat <- as.data.frame(cbind(contributions.candid, contributions.totals))

## Merge ##

dat1$conts.id <- (dat1$candid * 10000) + dat1$year

dat3 <- merge(dat1, contributions.dat, by.x = "conts.id",
              by.y = "contributions.candid", all.x = T)

dat3$tlfctr <- as.factor(dat3$pretl + 1)


### Compare Average Campaign Contributions ###
### Before/After term limits, and ntls too ###

dat.cc.88 <- dat3[which(dat3$year <= 1988),] # 34436 #
dat.cc.90 <- dat3[which(dat3$year >= 1990),] # 36975 #
dat.sp <- dat3[which(dat3$staffdiff >= 0),] # 23624 #
dat.sn <- dat3[which(dat3$staffdiff < 0),] # 23026 #


dat.cc.88.inc <- dat.cc.88[which(dat.cc.88$incumbent == 1),] # 18129 #
dat.cc.88.cha <- dat.cc.88[which(dat.cc.88$incumbent == 0),] # 16307 #
dat.cc.90.inc <- dat.cc.90[which(dat.cc.90$incumbent == 1),] # 20029 #
dat.cc.90.cha <- dat.cc.90[which(dat.cc.90$incumbent == 0),] # 16946 #


t.test(dat.cc.90.inc$contributions.totals ~ dat.cc.90.inc$tlfctr) # t= -4.4, meanx = 85367, meany = 112655 #
t.test(dat.cc.90.cha$contributions.totals ~ dat.cc.90.cha$tlfctr) # t= -4.4, meanx = 101123, meany = 138825 #


## staffing now ##

dat.sp.inc <- dat.sp[which(dat.sp$incumbent == 1),] # 13575 #
dat.sn.inc <- dat.sn[which(dat.sn$incumbent == 1),] # 12279 #
dat.sp.cha <- dat.sp[which(dat.sp$incumbent == 0),] # 10049 #
dat.sn.cha <- dat.sn[which(dat.sn$incumbent == 0),] # 10747 # 

mean(na.omit(dat.sp.inc$contributions.totals))

############################################
############################################

