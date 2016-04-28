#include <sys/cdefs.h>

#include <sys/socket.h>
#include <sys/sysctl.h>

#include <net/if.h>
#include <net/route.h>
#include <net/if_dl.h>
#include <netinet/in.h>
#include <arpa/inet.h>
#include <netdb.h>

#include <err.h>
#include <errno.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sysexits.h>
#include <unistd.h>
#include <ifaddrs.h>

union sockunion {
  struct  sockaddr sa;
  struct  sockaddr_in sin;
  struct  sockaddr_dl sdl;
  struct  sockaddr_storage ss; /* added to avoid memory overrun */
};

union sockunion so_dst, so_gate, so_mask, so_genmask, so_ifa, so_ifp;

typedef union sockunion *sup;
int pid, rtm_addrs, uid;
int s;
int forcehost, forcenet, nflag, af;
int iflag, verbose, aflen = sizeof (struct sockaddr_in);
int debugonly;
struct  rt_metrics rt_metrics;
u_long  rtm_inits;
unsigned int ifscope;

static const char *route_strerror(int);
void mask_addr();
void print_rtmsg(register struct rt_msghdr *rtm, int msglen);
int rtmsg(int cmd, int flags);
int getaddr(int which, char *s, struct hostent **hpp);
void sockaddr(register char *addr, register struct sockaddr *sa);
void newroute(char *cmd);
void sodump(register sup su, char *which);
void bprintf(register FILE *fp, register int b, register char *s);
const char *routename(struct sockaddr *sa);
void pmsg_addrs(char *cp, int addrs);
void pmsg_common(register struct rt_msghdr *rtm);
void print_getmsg(register struct rt_msghdr *rtm, int msglen);

void usage __P((const char *)) __dead2;

#define ROUNDUP(a) \
  ((a) > 0 ? (1 + (((a) - 1) | (sizeof(uint32_t) - 1))) : sizeof(uint32_t))
#define ADVANCE(x, n) (x += ROUNDUP((n)->sa_len))

int main(int argc, char **argv)
{
  s = socket(PF_ROUTE, SOCK_RAW, 0);

  if (s < 0) {
    err(EX_OSERR, "socket");
  }
  newroute("add");
}

void usage(const char *cp)
{
  if (cp)
    warnx("bad keyword: %s", cp);
  (void) fprintf(stderr,
                 "usage: route [-dnqtv] command [[modifiers] args]\n");
  exit(EX_USAGE);
  /* NOTREACHED */
}

static const char * route_strerror(int error) {
  switch (error) {
  case ESRCH:
    return "not in table";
  case EBUSY:
    return "entry in use";
  case ENOBUFS:
    return "routing table overflow";
  default:
    return (strerror(error));
  }
}

void newroute(char *cmd) {
  char *dest;
  char *gateway;

  int ishost = 0, ret, attempts, oerrno, flags = RTF_STATIC;
  struct hostent *hp = 0;

  if (uid) {
    errx(EX_NOPERM, "must be root to alter routing table");
  }

  dest = "10.0.0.30";
  ishost = getaddr(RTA_DST, dest, &hp);

  gateway = "192.168.66.128";
  getaddr(RTA_GATEWAY, gateway, &hp);

  if (forcenet) {
    ishost = 0;
  }

  flags |= RTF_UP;
  if (ishost) {
    flags |= RTF_HOST;
  }

  if (iflag == 0) {
    flags |= RTF_GATEWAY;
  }

  if (so_mask.sin.sin_family == AF_INET) { // renzo: saltato
    // make sure the mask is contiguous
    long i;
    for (i = 0; i < 32; i++) {
      if (((so_mask.sin.sin_addr.s_addr) & ntohl((1 << i))) != 0) {
        break;
      }
    }
    for (; i < 32; i++) {
      if (((so_mask.sin.sin_addr.s_addr) & ntohl((1 << i))) == 0) {
        errx(EX_NOHOST, "invalid mask: %s", inet_ntoa(so_mask.sin.sin_addr));
      }
    }
  }

  for (attempts = 1; ; attempts++) {
    errno = 0;
    if ((ret = rtmsg(*cmd, flags)) == 0) {
      break;
    }

    if (errno != ENETUNREACH && errno != ESRCH) { // renzo: ciclo fermato qui
      break;
    }

    if (af == AF_INET && *gateway && hp && hp->h_addr_list[1]) {
      hp->h_addr_list++;
      bcopy(hp->h_addr_list[0], &so_gate.sin.sin_addr, MIN(hp->h_length, sizeof(so_gate.sin.sin_addr)));
    } else {
      break;
    }
  }

  oerrno = errno;
  (void) printf("%s %s %s", cmd, ishost? "host" : "net", dest);

  if (*gateway) {
    (void) printf(": gateway %s", gateway);
    if (attempts > 1 && ret == 0 && af == AF_INET) {
      (void) printf(" (%s)", inet_ntoa(so_gate.sin.sin_addr));
    }
  }

  if (ret == 0) {
    (void) printf("\n");
  } else {
    (void)printf(": %s\n", route_strerror(oerrno));
  }
}

void inet_makenetandmask(in_addr_t net, register struct sockaddr_in *sin, in_addr_t bits)
{
  in_addr_t addr, mask = 0;
  register char *cp;

  rtm_addrs |= RTA_NETMASK;
  if (bits) {
    addr = net;
    mask = 0xffffffff << (32 - bits);
  } else if (net == 0)
    mask = addr = 0;
  else if (net < 128) {
    addr = net << IN_CLASSA_NSHIFT;
    mask = IN_CLASSA_NET;
  } else if (net < 65536) {
    addr = net << IN_CLASSB_NSHIFT;
    mask = IN_CLASSB_NET;
  } else if (net < 16777216L) {
    addr = net << IN_CLASSC_NSHIFT;
    mask = IN_CLASSC_NET;
  } else {
    addr = net;
    if ((addr & IN_CLASSA_HOST) == 0)
      mask =  IN_CLASSA_NET;
    else if ((addr & IN_CLASSB_HOST) == 0)
      mask =  IN_CLASSB_NET;
    else if ((addr & IN_CLASSC_HOST) == 0)
      mask =  IN_CLASSC_NET;
    else
      mask = -1;
  }
  sin->sin_addr.s_addr = htonl(addr);
  sin = &so_mask.sin;
  sin->sin_addr.s_addr = htonl(mask);
  sin->sin_len = 0;
  sin->sin_family = 0;
  cp = (char *)(&sin->sin_addr + 1);
  while (*--cp == 0 && cp > (char *)sin)
    ;
  sin->sin_len = 1 + cp - (char *)sin;
}


/*
 * Interpret an argument as a network address of some kind,
 * returning 1 if a host address, 0 if a network address.
 */
int getaddr(int which, char *s, struct hostent **hpp)
{
  register sup su = NULL;
  struct hostent *hp;
  struct netent *np;
  in_addr_t val;
  char *q;
  int afamily;  /* local copy of af so we can change it */

  if (af == 0) {
    af = AF_INET;
    aflen = sizeof(struct sockaddr_in);
  }
  afamily = af;
  rtm_addrs |= which;
  switch (which) {
  case RTA_DST:
    su = &so_dst;
    break;
  case RTA_GATEWAY:
    su = &so_gate;
    if (iflag) {
      struct ifaddrs *ifap, *ifa;
      struct sockaddr_dl *sdl = NULL;

      if (getifaddrs(&ifap))
        err(1, "getifaddrs");

      for (ifa = ifap; ifa; ifa = ifa->ifa_next) {
        if (ifa->ifa_addr->sa_family != AF_LINK)
          continue;

        if (strcmp(s, ifa->ifa_name))
          continue;

        sdl = (struct sockaddr_dl *)ifa->ifa_addr;
      }
      /* If we found it, then use it */
      if (sdl) {
        /*
         * Copy is safe since we have a
         * sockaddr_storage member in sockunion{}.
         * Note that we need to copy before calling
         * freeifaddrs().
         */
        memcpy(&su->sdl, sdl, sdl->sdl_len);
      }
      freeifaddrs(ifap);
      if (sdl)
        return(1);
    }
    break;
  case RTA_NETMASK:
    su = &so_mask;
    break;
  case RTA_GENMASK:
    su = &so_genmask;
    break;
  case RTA_IFP:
    su = &so_ifp;
    afamily = AF_LINK;
    break;
  case RTA_IFA:
    su = &so_ifa;
    break;
  default:
    usage("internal error");
    /*NOTREACHED*/
  }
  su->sa.sa_len = aflen;
  su->sa.sa_family = afamily; /* cases that don't want it have left already */
  if (strcmp(s, "default") == 0) {
    /*
     * Default is net 0.0.0.0/0 
     */
    switch (which) {
    case RTA_DST:
      forcenet++;
      /* bzero(su, sizeof(*su)); *//* for readability */
      (void) getaddr(RTA_NETMASK, s, 0);
      break;
    case RTA_NETMASK:
    case RTA_GENMASK:
      /* bzero(su, sizeof(*su)); *//* for readability */
      su->sa.sa_len = 0;
      break;
    }
    return (0);
  }
  switch (afamily) {
  case AF_LINK:
    link_addr(s, &su->sdl);
    return (1);


  case PF_ROUTE:
    su->sa.sa_len = sizeof(*su);
    sockaddr(s, &su->sa);
    return (1);

  case AF_INET:
  default:
    break;
  }

  if (hpp == NULL) {
    hpp = &hp;
  }
  *hpp = NULL;

  q = strchr(s,'/');
  if (q && which == RTA_DST) {
    *q = '\0';
    if ((val = inet_addr(s)) != INADDR_NONE) {
      inet_makenetandmask(
        ntohl(val), &su->sin, strtoul(q+1, 0, 0));
      return (0);
    }
    *q = '/';
  }
  if ((which != RTA_DST || forcenet == 0) &&
      (val = inet_addr(s)) != INADDR_NONE) {
    su->sin.sin_addr.s_addr = val;
    if (which != RTA_DST ||
        inet_lnaof(su->sin.sin_addr) != INADDR_ANY)
      return (1);
    else {
      val = ntohl(val);
      goto netdone;
    }
  }
  if (which == RTA_DST && forcehost == 0 &&
      ((val = inet_network(s)) != INADDR_NONE ||
      ((np = getnetbyname(s)) != NULL && (val = np->n_net) != 0))) {
netdone:
    inet_makenetandmask(val, &su->sin, 0);
    return (0);
  }
  hp = gethostbyname(s);
  if (hp) {
    *hpp = hp;
    su->sin.sin_family = hp->h_addrtype;
    bcopy(hp->h_addr, (char *)&su->sin.sin_addr, 
        MIN(hp->h_length, sizeof(su->sin.sin_addr)));
    return (1);
  }
  errx(EX_NOHOST, "bad address: %s", s);
}

struct {
  struct  rt_msghdr m_rtm;
  char  m_space[512];
} m_rtmsg;

int rtmsg(int cmd, int flags) {
  static int seq;
  int rlen;
  register char *cp = m_rtmsg.m_space;
  register int l;

#define NEXTADDR(w, u) \
  if (rtm_addrs & (w)) {\
      l = ROUNDUP(u.sa.sa_len); bcopy((char *)&(u), cp, l); cp += l;\
      if (verbose) sodump(&(u),"u");\
  }

  errno = 0;
  bzero((char *)&m_rtmsg, sizeof(m_rtmsg));
  if (cmd == 'a')
    cmd = RTM_ADD;
  else if (cmd == 'c')
    cmd = RTM_CHANGE;
  else if (cmd == 'g') {
    cmd = RTM_GET;
    if (so_ifp.sa.sa_family == 0) {
      so_ifp.sa.sa_family = AF_LINK;
      so_ifp.sa.sa_len = sizeof(struct sockaddr_dl);
      rtm_addrs |= RTA_IFP;
    }
  } else
    cmd = RTM_DELETE;
#define rtm m_rtmsg.m_rtm
  rtm.rtm_type = cmd;
  rtm.rtm_flags = flags;
  rtm.rtm_version = RTM_VERSION;
  rtm.rtm_seq = ++seq;
  rtm.rtm_addrs = rtm_addrs;
  rtm.rtm_rmx = rt_metrics;
  rtm.rtm_inits = rtm_inits;
  rtm.rtm_index = ifscope;

  if (rtm_addrs & RTA_NETMASK)
    mask_addr();
  NEXTADDR(RTA_DST, so_dst);
  NEXTADDR(RTA_GATEWAY, so_gate);
  NEXTADDR(RTA_NETMASK, so_mask);
  NEXTADDR(RTA_GENMASK, so_genmask);
  NEXTADDR(RTA_IFP, so_ifp);
  NEXTADDR(RTA_IFA, so_ifa);
  rtm.rtm_msglen = l = cp - (char *)&m_rtmsg;
  if (verbose)
    print_rtmsg(&rtm, l);
  if (debugonly)
    return (0);

  // TODO: check here, should be where its actually made the write
  if ((rlen = write(s, (char *)&m_rtmsg, l)) < 0) {
    warnx("writing to routing socket: %s", route_strerror(errno));
    return (-1);
  }
  if (cmd == RTM_GET) {
    do {
      l = read(s, (char *)&m_rtmsg, sizeof(m_rtmsg));
    } while (l > 0 && (rtm.rtm_seq != seq || rtm.rtm_pid != pid));
    if (l < 0)
      warn("read from routing socket");
    else
      print_getmsg(&rtm, l);
  }
#undef rtm
  return (0);
}

void mask_addr() {
  int olen = so_mask.sa.sa_len;
  register char *cp1 = olen + (char *)&so_mask, *cp2;

  for (so_mask.sa.sa_len = 0; cp1 > (char *)&so_mask; )
    if (*--cp1 != 0) {
      so_mask.sa.sa_len = 1 + cp1 - (char *)&so_mask;
      break;
    }
  if ((rtm_addrs & RTA_DST) == 0)
    return;
  switch (so_dst.sa.sa_family) {
  case AF_INET:
#ifdef INET6
  case AF_INET6:
#endif
  case AF_APPLETALK:
  case 0:
    return;
  }
  cp1 = so_mask.sa.sa_len + 1 + (char *)&so_dst;
  cp2 = so_dst.sa.sa_len + 1 + (char *)&so_dst;
  while (cp2 > cp1)
    *--cp2 = 0;
  cp2 = so_mask.sa.sa_len + 1 + (char *)&so_mask;
  while (cp1 > so_dst.sa.sa_data)
    *--cp1 &= *--cp2;
}

char *msgtypes[] = {
  "",
  "RTM_ADD: Add Route",
  "RTM_DELETE: Delete Route",
  "RTM_CHANGE: Change Metrics or flags",
  "RTM_GET: Report Metrics",
  "RTM_LOSING: Kernel Suspects Partitioning",
  "RTM_REDIRECT: Told to use different route",
  "RTM_MISS: Lookup failed on this address",
  "RTM_LOCK: fix specified metrics",
  "RTM_OLDADD: caused by SIOCADDRT",
  "RTM_OLDDEL: caused by SIOCDELRT",
  "RTM_RESOLVE: Route created by cloning",
  "RTM_NEWADDR: address being added to iface",
  "RTM_DELADDR: address being removed from iface",
  "RTM_IFINFO: iface status change",
  "RTM_NEWMADDR: new multicast group membership on iface",
  "RTM_DELMADDR: multicast group membership removed from iface",
  0,
};

char metricnames[] =
"\011pksent\010rttvar\7rtt\6ssthresh\5sendpipe\4recvpipe\3expire\2hopcount"
"\1mtu";
char routeflags[] =
"\1UP\2GATEWAY\3HOST\4REJECT\5DYNAMIC\6MODIFIED\7DONE\010DELCLONE"
"\011CLONING\012XRESOLVE\013LLINFO\014STATIC\015BLACKHOLE\016b016"
"\017PROTO2\020PROTO1\021PRCLONING\022WASCLONED\023PROTO3\024b024"
"\025PINNED\026LOCAL\027BROADCAST\030MULTICAST\031IFSCOPE\032CONDEMNED"
"\033IFREF\034PROXY\035ROUTER";
char ifnetflags[] =
"\1UP\2BROADCAST\3DEBUG\4LOOPBACK\5PTP\6b6\7RUNNING\010NOARP"
"\011PPROMISC\012ALLMULTI\013OACTIVE\014SIMPLEX\015LINK0\016LINK1"
"\017LINK2\020MULTICAST";
char addrnames[] =
"\1DST\2GATEWAY\3NETMASK\4GENMASK\5IFP\6IFA\7AUTHOR\010BRD";

void print_rtmsg(register struct rt_msghdr *rtm, int msglen)
{
  struct if_msghdr *ifm;
  struct ifa_msghdr *ifam;
#ifdef RTM_NEWMADDR
  struct ifma_msghdr *ifmam;
#endif

  if (verbose == 0)
    return;
  if (rtm->rtm_version != RTM_VERSION) {
    (void) printf("routing message version %d not understood\n",
        rtm->rtm_version);
    return;
  }
  (void)printf("%s: len %d, ", msgtypes[rtm->rtm_type], rtm->rtm_msglen);
  switch (rtm->rtm_type) {
  case RTM_IFINFO:
    ifm = (struct if_msghdr *)rtm;
    (void) printf("if# %d, flags:", ifm->ifm_index);
    bprintf(stdout, ifm->ifm_flags, ifnetflags);
    pmsg_addrs((char *)(ifm + 1), ifm->ifm_addrs);
    break;
  case RTM_NEWADDR:
  case RTM_DELADDR:
    ifam = (struct ifa_msghdr *)rtm;
    (void) printf("metric %d, flags:", ifam->ifam_metric);
    bprintf(stdout, ifam->ifam_flags, routeflags);
    pmsg_addrs((char *)(ifam + 1), ifam->ifam_addrs);
    break;
#ifdef RTM_NEWMADDR
  case RTM_NEWMADDR:
  case RTM_DELMADDR:
    ifmam = (struct ifma_msghdr *)rtm;
    pmsg_addrs((char *)(ifmam + 1), ifmam->ifmam_addrs);
    break;
#endif
  default:
    (void) printf("pid: %ld, seq %d, errno %d, ",
      (long)rtm->rtm_pid, rtm->rtm_seq, rtm->rtm_errno);
    if (rtm->rtm_flags & RTF_IFSCOPE)
      (void) printf("ifscope %d, ", rtm->rtm_index);
      if (rtm->rtm_flags & RTF_IFREF)
      (void) printf("ifref, ");
      (void) printf("flags:");
    bprintf(stdout, rtm->rtm_flags, routeflags);
    pmsg_common(rtm);
  }
}

void print_getmsg(register struct rt_msghdr *rtm, int msglen)
{
  struct sockaddr *dst = NULL, *gate = NULL, *mask = NULL;
  struct sockaddr_dl *ifp = NULL;
  register struct sockaddr *sa;
  register char *cp;
  register int i;

  (void) printf("   route to: %s\n", routename(&so_dst.sa));
  if (rtm->rtm_version != RTM_VERSION) {
    warnx("routing message version %d not understood",
         rtm->rtm_version);
    return;
  }
  if (rtm->rtm_msglen > msglen) {
    warnx("message length mismatch, in packet %d, returned %d",
          rtm->rtm_msglen, msglen);
  }
  if (rtm->rtm_errno)  {
    errno = rtm->rtm_errno;
    warn("message indicates error %d", errno);
    return;
  }
  cp = ((char *)(rtm + 1));
  if (rtm->rtm_addrs)
    for (i = 1; i; i <<= 1)
      if (i & rtm->rtm_addrs) {
        sa = (struct sockaddr *)cp;
        switch (i) {
        case RTA_DST:
          dst = sa;
          break;
        case RTA_GATEWAY:
          gate = sa;
          break;
        case RTA_NETMASK:
          mask = sa;
          break;
        case RTA_IFP:
          if (sa->sa_family == AF_LINK &&
             ((struct sockaddr_dl *)sa)->sdl_nlen)
            ifp = (struct sockaddr_dl *)sa;
          break;
        }
        ADVANCE(cp, sa);
      }
  if (dst && mask)
    mask->sa_family = dst->sa_family; /* XXX */
  if (dst)
    (void)printf("destination: %s\n", routename(dst));
  if (mask) {
    int savenflag = nflag;

    nflag = 1;
    (void)printf("       mask: %s\n", routename(mask));
    nflag = savenflag;
  }
  if (gate && rtm->rtm_flags & RTF_GATEWAY)
    (void)printf("    gateway: %s\n", routename(gate));
  if (ifp)
    (void)printf("  interface: %.*s\n",
        ifp->sdl_nlen, ifp->sdl_data);
  (void)printf("      flags: ");
  bprintf(stdout, rtm->rtm_flags, routeflags);

#define lock(f) ((rtm->rtm_rmx.rmx_locks & __CONCAT(RTV_,f)) ? 'L' : ' ')
#define msec(u) (((u) + 500) / 1000)    /* usec to msec */

  (void) printf("\n%s\n", "\
 recvpipe  sendpipe  ssthresh  rtt,msec    rttvar  hopcount      mtu     expire");
  printf("%8u%c ", rtm->rtm_rmx.rmx_recvpipe, lock(RPIPE));
  printf("%8u%c ", rtm->rtm_rmx.rmx_sendpipe, lock(SPIPE));
  printf("%8u%c ", rtm->rtm_rmx.rmx_ssthresh, lock(SSTHRESH));
  printf("%8u%c ", msec(rtm->rtm_rmx.rmx_rtt), lock(RTT));
  printf("%8u%c ", msec(rtm->rtm_rmx.rmx_rttvar), lock(RTTVAR));
  printf("%8u%c ", rtm->rtm_rmx.rmx_hopcount, lock(HOPCOUNT));
  printf("%8u%c ", rtm->rtm_rmx.rmx_mtu, lock(MTU));
  if (rtm->rtm_rmx.rmx_expire)
    rtm->rtm_rmx.rmx_expire -= time(0);
  printf("%8d%c\n", rtm->rtm_rmx.rmx_expire, lock(EXPIRE));
#undef lock
#undef msec
#define RTA_IGN (RTA_DST|RTA_GATEWAY|RTA_NETMASK|RTA_IFP|RTA_IFA|RTA_BRD)
  if (verbose)
    pmsg_common(rtm);
  else if (rtm->rtm_addrs &~ RTA_IGN) {
    (void) printf("sockaddrs: ");
    bprintf(stdout, rtm->rtm_addrs, addrnames);
    putchar('\n');
  }
#undef  RTA_IGN
}

void pmsg_common(register struct rt_msghdr *rtm)
{
  (void) printf("\nlocks: ");
  bprintf(stdout, rtm->rtm_rmx.rmx_locks, metricnames);
  (void) printf(" inits: ");
  bprintf(stdout, rtm->rtm_inits, metricnames);
  pmsg_addrs(((char *)(rtm + 1)), rtm->rtm_addrs);
}

void pmsg_addrs(char *cp, int addrs)
{
  register struct sockaddr *sa;
  int i;

  if (addrs == 0) {
    (void) putchar('\n');
    return;
  }
  (void) printf("\nsockaddrs: ");
  bprintf(stdout, addrs, addrnames);
  (void) putchar('\n');
  for (i = 1; i; i <<= 1)
    if (i & addrs) {
      sa = (struct sockaddr *)cp;
      (void) printf(" %s", routename(sa));
      ADVANCE(cp, sa);
    }
  (void) putchar('\n');
  (void) fflush(stdout);
}

void bprintf(register FILE *fp, register int b, register char *s)
{
  register int i;
  int gotsome = 0;

  if (b == 0)
    return;
  while ((i = *s++) != 0) {
    if (b & (1 << (i-1))) {
      if (gotsome == 0)
        i = '<';
      else
        i = ',';
      (void) putc(i, fp);
      gotsome = 1;
      for (; (i = *s) > 32; s++)
        (void) putc(i, fp);
    } else
      while (*s > 32)
        s++;
  }
  if (gotsome)
    (void) putc('>', fp);
}

void sodump(register sup su, char *which)
{
  switch (su->sa.sa_family) {
  case AF_LINK:
    (void) printf("%s: link %s; ",
        which, link_ntoa(&su->sdl));
    break;
  case AF_INET:
    (void) printf("%s: inet %s; ",
        which, inet_ntoa(su->sin.sin_addr));
    break;
  }
  (void) fflush(stdout);
}

/* States*/
#define VIRGIN  0
#define GOTONE  1
#define GOTTWO  2
/* Inputs */
#define DIGIT (4*0)
#define END (4*1)
#define DELIM (4*2)

void sockaddr(register char *addr, register struct sockaddr *sa)
{
  register char *cp = (char *)sa;
  int size = sa->sa_len;
  char *cplim = cp + size;
  register int byte = 0, state = VIRGIN, new = 0 /* foil gcc */;

  bzero(cp, size);
  cp++;
  do {
    if ((*addr >= '0') && (*addr <= '9')) {
      new = *addr - '0';
    } else if ((*addr >= 'a') && (*addr <= 'f')) {
      new = *addr - 'a' + 10;
    } else if ((*addr >= 'A') && (*addr <= 'F')) {
      new = *addr - 'A' + 10;
    } else if (*addr == 0)
      state |= END;
    else
      state |= DELIM;
    addr++;
    switch (state /* | INPUT */) {
    case GOTTWO | DIGIT:
      *cp++ = byte; /*FALLTHROUGH*/
    case VIRGIN | DIGIT:
      state = GOTONE; byte = new; continue;
    case GOTONE | DIGIT:
      state = GOTTWO; byte = new + (byte << 4); continue;
    default: /* | DELIM */
      state = VIRGIN; *cp++ = byte; byte = 0; continue;
    case GOTONE | END:
    case GOTTWO | END:
      *cp++ = byte; /* FALLTHROUGH */
    case VIRGIN | END:
      break;
    }
    break;
  } while (cp < cplim);
  sa->sa_len = cp - (char *)sa;
}

const char *routename(struct sockaddr *sa) {
  register char *cp;
  static char line[MAXHOSTNAMELEN + 1];
  struct hostent *hp;
  static char domain[MAXHOSTNAMELEN + 1];
  static int first = 1;

  if (first) {
    first = 0;
    if (gethostname(domain, MAXHOSTNAMELEN) == 0 &&
        (cp = index(domain, '.'))) {
      domain[MAXHOSTNAMELEN] = '\0';
      (void) memmove(domain, cp + 1, strlen(cp + 1) + 1);
    } else
      domain[0] = 0;
  }

  if (sa->sa_len == 0)
    strlcpy(line, "default", sizeof(line));
  else switch (sa->sa_family) {

      case AF_INET:
      { struct in_addr in;
        in = ((struct sockaddr_in *)sa)->sin_addr;

        cp = 0;
        if (in.s_addr == INADDR_ANY || sa->sa_len < 4)
          cp = "default";
        if (cp == 0 && !nflag) {
          hp = gethostbyaddr((char *)&in, sizeof (struct in_addr),
                             AF_INET);
          if (hp) {
            if ((cp = index(hp->h_name, '.')) &&
                !strcmp(cp + 1, domain))
              *cp = 0;
            cp = hp->h_name;
          }
        }
        if (cp) {
          strncpy(line, cp, sizeof(line) - 1);
          line[sizeof(line) - 1] = '\0';
        } else {
          /* XXX - why not inet_ntoa()? */
#define C(x)  (unsigned)((x) & 0xff)
          in.s_addr = ntohl(in.s_addr);
          (void) snprintf(line, sizeof(line), "%u.%u.%u.%u", C(in.s_addr >> 24),
                          C(in.s_addr >> 16), C(in.s_addr >> 8), C(in.s_addr));
        }
        break;
      }

      case AF_LINK:
        return (link_ntoa((struct sockaddr_dl *)sa));

      default:
      { u_short *s = (u_short *)sa;
        u_short *slim = s + ((sa->sa_len + 1) >> 1);
        char *cp = line + snprintf(line, sizeof(line), "(%d)", sa->sa_family);
        char *cpe = line + sizeof(line);

        while (++s < slim && cp < cpe) /* start with sa->sa_data */
          cp += snprintf(cp, cpe - cp, " %x", *s);
        break;
      }
    }
  return (line);
}
