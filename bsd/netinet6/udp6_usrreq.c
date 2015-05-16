/*
 * Copyright (c) 2000-2013 Apple Inc. All rights reserved.
 *
 * @APPLE_OSREFERENCE_LICENSE_HEADER_START@
 * 
 * This file contains Original Code and/or Modifications of Original Code
 * as defined in and that are subject to the Apple Public Source License
 * Version 2.0 (the 'License'). You may not use this file except in
 * compliance with the License. The rights granted to you under the License
 * may not be used to create, or enable the creation or redistribution of,
 * unlawful or unlicensed copies of an Apple operating system, or to
 * circumvent, violate, or enable the circumvention or violation of, any
 * terms of an Apple operating system software license agreement.
 * 
 * Please obtain a copy of the License at
 * http://www.opensource.apple.com/apsl/ and read it before using this file.
 * 
 * The Original Code and all software distributed under the License are
 * distributed on an 'AS IS' basis, WITHOUT WARRANTY OF ANY KIND, EITHER
 * EXPRESS OR IMPLIED, AND APPLE HEREBY DISCLAIMS ALL SUCH WARRANTIES,
 * INCLUDING WITHOUT LIMITATION, ANY WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE, QUIET ENJOYMENT OR NON-INFRINGEMENT.
 * Please see the License for the specific language governing rights and
 * limitations under the License.
 * 
 * @APPLE_OSREFERENCE_LICENSE_HEADER_END@
 */

/*	$FreeBSD: src/sys/netinet6/udp6_usrreq.c,v 1.6.2.6 2001/07/29 19:32:40 ume Exp $	*/
/*	$KAME: udp6_usrreq.c,v 1.27 2001/05/21 05:45:10 jinmei Exp $	*/

/*
 * Copyright (C) 1995, 1996, 1997, and 1998 WIDE Project.
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 * 1. Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the distribution.
 * 3. Neither the name of the project nor the names of its contributors
 *    may be used to endorse or promote products derived from this software
 *    without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE PROJECT AND CONTRIBUTORS ``AS IS'' AND
 * ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
 * ARE DISCLAIMED.  IN NO EVENT SHALL THE PROJECT OR CONTRIBUTORS BE LIABLE
 * FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS
 * OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)
 * HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT
 * LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY
 * OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF
 * SUCH DAMAGE.
 */

/*
 * Copyright (c) 1982, 1986, 1989, 1993
 *	The Regents of the University of California.  All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 * 1. Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the distribution.
 * 3. All advertising materials mentioning features or use of this software
 *    must display the following acknowledgement:
 *	This product includes software developed by the University of
 *	California, Berkeley and its contributors.
 * 4. Neither the name of the University nor the names of its contributors
 *    may be used to endorse or promote products derived from this software
 *    without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE REGENTS AND CONTRIBUTORS ``AS IS'' AND
 * ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
 * ARE DISCLAIMED.  IN NO EVENT SHALL THE REGENTS OR CONTRIBUTORS BE LIABLE
 * FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS
 * OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)
 * HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT
 * LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY
 * OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF
 * SUCH DAMAGE.
 *
 *	@(#)udp_var.h	8.1 (Berkeley) 6/10/93
 */

#include <sys/param.h>
#include <sys/kernel.h>
#include <sys/malloc.h>
#include <sys/mbuf.h>
#include <sys/protosw.h>
#include <sys/socket.h>
#include <sys/socketvar.h>
#include <sys/sysctl.h>
#include <sys/errno.h>
#include <sys/stat.h>
#include <sys/systm.h>
#include <sys/syslog.h>
#include <sys/proc.h>
#include <sys/kauth.h>

#include <net/if.h>
#include <net/route.h>
#include <net/if_types.h>
#include <net/ntstat.h>
#include <net/dlil.h>

#include <netinet/in.h>
#include <netinet/in_systm.h>
#include <netinet/ip.h>
#include <netinet/in_pcb.h>
#include <netinet/in_var.h>
#include <netinet/ip_var.h>
#include <netinet/udp.h>
#include <netinet/udp_var.h>
#include <netinet/ip6.h>
#include <netinet6/ip6_var.h>
#include <netinet6/in6_pcb.h>
#include <netinet/icmp6.h>
#include <netinet6/udp6_var.h>
#include <netinet6/ip6protosw.h>

#if IPSEC
#include <netinet6/ipsec.h>
#include <netinet6/ipsec6.h>
extern int ipsec_bypass;
#endif /* IPSEC */

/*
 * UDP protocol inplementation.
 * Per RFC 768, August, 1980.
 */

static int udp6_abort(struct socket *);
static int udp6_attach(struct socket *, int, struct proc *);
static int udp6_bind(struct socket *, struct sockaddr *, struct proc *);
static int udp6_connectx(struct socket *, struct sockaddr_list **,
    struct sockaddr_list **, struct proc *, uint32_t, associd_t, connid_t *,
    uint32_t, void *, uint32_t);
static	int udp6_detach(struct socket *);
static int udp6_disconnect(struct socket *);
static int udp6_disconnectx(struct socket *, associd_t, connid_t);
static int udp6_send(struct socket *, int, struct mbuf *, struct sockaddr *,
    struct mbuf *, struct proc *);
static void udp6_append(struct inpcb *, struct ip6_hdr *,
    struct sockaddr_in6 *, struct mbuf *, int, struct ifnet *);
static int udp6_input_checksum(struct mbuf *, struct udphdr *, int, int);

#if IPFIREWALL
extern int fw_verbose;
extern void ipfwsyslog( int level, const char *format,...);
extern void ipfw_stealth_stats_incr_udpv6(void);

/* Apple logging, log to ipfw.log */
#define log_in_vain_log(a) {						\
	if ((udp_log_in_vain == 3) && (fw_verbose == 2)) {		\
		ipfwsyslog a;						\
        } else if ((udp_log_in_vain == 4) && (fw_verbose == 2)) {       \
	        ipfw_stealth_stats_incr_udpv6();			\
	} else {							\
		log a;							\
	}								\
}
#else /* !IPFIREWALL */
#define log_in_vain_log( a ) { log a; }
#endif /* !IPFIREWALL */

struct pr_usrreqs udp6_usrreqs = {
	.pru_abort =		udp6_abort,
	.pru_attach =		udp6_attach,
	.pru_bind =		udp6_bind,
	.pru_connect =		udp6_connect,
	.pru_connectx =		udp6_connectx,
	.pru_control =		in6_control,
	.pru_detach =		udp6_detach,
	.pru_disconnect =	udp6_disconnect,
	.pru_disconnectx =	udp6_disconnectx,
	.pru_peeraddr =		in6_mapped_peeraddr,
	.pru_send =		udp6_send,
	.pru_shutdown =		udp_shutdown,
	.pru_sockaddr =		in6_mapped_sockaddr,
	.pru_sosend =		sosend,
	.pru_soreceive =	soreceive,
};

/*
 * subroutine of udp6_input(), mainly for source code readability.
 */
static void
udp6_append(struct inpcb *last, struct ip6_hdr *ip6,
    struct sockaddr_in6 *udp_in6, struct mbuf *n, int off, struct ifnet *ifp)
{
#pragma unused(ip6)
	struct  mbuf *opts = NULL;
	int ret = 0;
	boolean_t cell = IFNET_IS_CELLULAR(ifp);
	boolean_t wifi = (!cell && IFNET_IS_WIFI(ifp));

#if CONFIG_MACF_NET
	if (mac_inpcb_check_deliver(last, n, AF_INET6, SOCK_DGRAM) != 0) {
		m_freem(n);
		return;
	}
#endif /* CONFIG_MACF_NET */
	if ((last->in6p_flags & INP_CONTROLOPTS) != 0 ||
	    (last->in6p_socket->so_options & SO_TIMESTAMP) != 0 ||
	    (last->in6p_socket->so_options & SO_TIMESTAMP_MONOTONIC) != 0) {
		ret = ip6_savecontrol(last, n, &opts);
		if (ret != 0) {
			m_freem(n);
			m_freem(opts);
			return;
		}
	}
	m_adj(n, off);
	if (nstat_collect) {
		INP_ADD_STAT(last, cell, wifi, rxpackets, 1);
		INP_ADD_STAT(last, cell, wifi, rxbytes, n->m_pkthdr.len);
	}
	so_recv_data_stat(last->in6p_socket, n, 0);
	if (sbappendaddr(&last->in6p_socket->so_rcv,
	    (struct sockaddr *)udp_in6, n, opts, NULL) == 0)
		udpstat.udps_fullsock++;
	else
		sorwakeup(last->in6p_socket);
}

int
udp6_input(struct mbuf **mp, int *offp, int proto)
{
#pragma unused(proto)
	struct mbuf *m = *mp;
	struct ifnet *ifp;
	struct ip6_hdr *ip6;
	struct udphdr *uh;
	struct inpcb *in6p;
	struct  mbuf *opts = NULL;
	int off = *offp;
	int plen, ulen, ret = 0;
	boolean_t cell, wifi;
	struct sockaddr_in6 udp_in6;
	struct inpcbinfo *pcbinfo = &udbinfo;
	struct sockaddr_in6 fromsa;

	IP6_EXTHDR_CHECK(m, off, sizeof (struct udphdr), return IPPROTO_DONE);

	/* Expect 32-bit aligned data pointer on strict-align platforms */
	MBUF_STRICT_DATA_ALIGNMENT_CHECK_32(m);

	ifp = m->m_pkthdr.rcvif;
	ip6 = mtod(m, struct ip6_hdr *);
	cell = IFNET_IS_CELLULAR(ifp);
	wifi = (!cell && IFNET_IS_WIFI(ifp));

	udpstat.udps_ipackets++;

	plen = ntohs(ip6->ip6_plen) - off + sizeof (*ip6);
	uh = (struct udphdr *)(void *)((caddr_t)ip6 + off);
	ulen = ntohs((u_short)uh->uh_ulen);

	if (plen != ulen) {
		udpstat.udps_badlen++;
		IF_UDP_STATINC(ifp, badlength);
		goto bad;
	}

	/* destination port of 0 is illegal, based on RFC768. */
	if (uh->uh_dport == 0) {
		IF_UDP_STATINC(ifp, port0);
		goto bad;
	}

	/*
	 * Checksum extended UDP header and data.
	 */
	if (udp6_input_checksum(m, uh, off, ulen))
		goto bad;

	/*
	 * Construct sockaddr format source address.
	 */
	init_sin6(&fromsa, m);
	fromsa.sin6_port = uh->uh_sport;

	if (IN6_IS_ADDR_MULTICAST(&ip6->ip6_dst)) {
		int reuse_sock = 0, mcast_delivered = 0;
		struct ip6_moptions *imo;
		struct mbuf *n = NULL;

		/*
		 * Deliver a multicast datagram to all sockets
		 * for which the local and remote addresses and ports match
		 * those of the incoming datagram.  This allows more than
		 * one process to receive multicasts on the same port.
		 * (This really ought to be done for unicast datagrams as
		 * well, but that would cause problems with existing
		 * applications that open both address-specific sockets and
		 * a wildcard socket listening to the same port -- they would
		 * end up receiving duplicates of every unicast datagram.
		 * Those applications open the multiple sockets to overcome an
		 * inadequacy of the UDP socket interface, but for backwards
		 * compatibility we avoid the problem here rather than
		 * fixing the interface.  Maybe 4.5BSD will remedy this?)
		 */

		/*
		 * In a case that laddr should be set to the link-local
		 * address (this happens in RIPng), the multicast address
		 * specified in the received packet does not match with
		 * laddr. To cure this situation, the matching is relaxed
		 * if the receiving interface is the same as one specified
		 * in the socket and if the destination multicast address
		 * matches one of the multicast groups specified in the socket.
		 */

		/*
		 * Construct sockaddr format source address.
		 */
		init_sin6(&udp_in6, m); /* general init */
		udp_in6.sin6_port = uh->uh_sport;
		/*
		 * KAME note: usually we drop udphdr from mbuf here.
		 * We need udphdr for IPsec processing so we do that later.
		 */

		/*
		 * Locate pcb(s) for datagram.
		 * (Algorithm copied from raw_intr().)
		 */
		lck_rw_lock_shared(pcbinfo->ipi_lock);

		LIST_FOREACH(in6p, &udb, inp_list) {
#if IPSEC
			int skipit;
#endif /* IPSEC */

			if ((in6p->inp_vflag & INP_IPV6) == 0)
				continue;

			if (inp_restricted(in6p, ifp))
				continue;

			if (IFNET_IS_CELLULAR(ifp) &&
			    (in6p->in6p_flags & INP_NO_IFT_CELLULAR))
				continue;

			if (in_pcb_checkstate(in6p, WNT_ACQUIRE, 0) ==
			    WNT_STOPUSING)
				continue;

			udp_lock(in6p->in6p_socket, 1, 0);

			if (in_pcb_checkstate(in6p, WNT_RELEASE, 1) ==
			    WNT_STOPUSING) {
				udp_unlock(in6p->in6p_socket, 1, 0);
				continue;
			}
			if (in6p->in6p_lport != uh->uh_dport) {
				udp_unlock(in6p->in6p_socket, 1, 0);
				continue;
			}

			/*
			 * Handle socket delivery policy for any-source
			 * and source-specific multicast. [RFC3678]
			 */
			imo = in6p->in6p_moptions;
			if (imo && IN6_IS_ADDR_MULTICAST(&ip6->ip6_dst)) {
				struct sockaddr_in6 mcaddr;
				int blocked;

				IM6O_LOCK(imo);
				bzero(&mcaddr, sizeof (struct sockaddr_in6));
				mcaddr.sin6_len = sizeof (struct sockaddr_in6);
				mcaddr.sin6_family = AF_INET6;
				mcaddr.sin6_addr = ip6->ip6_dst;

				blocked = im6o_mc_filter(imo, ifp,
				    (struct sockaddr *)&mcaddr,
				    (struct sockaddr *)&fromsa);
				IM6O_UNLOCK(imo);
				if (blocked != MCAST_PASS) {
					udp_unlock(in6p->in6p_socket, 1, 0);
					if (blocked == MCAST_NOTSMEMBER ||
					    blocked == MCAST_MUTED)
						udpstat.udps_filtermcast++;
					continue;
				}
			}
			if (!IN6_IS_ADDR_UNSPECIFIED(&in6p->in6p_faddr) &&
			    (!IN6_ARE_ADDR_EQUAL(&in6p->in6p_faddr,
			    &ip6->ip6_src) ||
			    in6p->in6p_fport != uh->uh_sport)) {
				udp_unlock(in6p->in6p_socket, 1, 0);
				continue;
			}

			reuse_sock = in6p->inp_socket->so_options &
			    (SO_REUSEPORT | SO_REUSEADDR);

#if IPSEC
			skipit = 0;
			/* Check AH/ESP integrity. */
			if (ipsec_bypass == 0 &&
			    ipsec6_in_reject_so(m, in6p->inp_socket)) {
				IPSEC_STAT_INCREMENT(ipsec6stat.in_polvio);
				/* do not inject data to pcb */
				skipit = 1;
			}
			if (skipit == 0)
#endif /* IPSEC */
			{
				/*
				 * KAME NOTE: do not
				 * m_copy(m, offset, ...) below.
				 * sbappendaddr() expects M_PKTHDR,
				 * and m_copy() will copy M_PKTHDR
				 * only if offset is 0.
				 */
				if (reuse_sock)
					n = m_copy(m, 0, M_COPYALL);
				udp6_append(in6p, ip6, &udp_in6, m,
				    off + sizeof (struct udphdr), ifp);
				mcast_delivered++;
			}
			udp_unlock(in6p->in6p_socket, 1, 0);

			/*
			 * Don't look for additional matches if this one does
			 * not have either the SO_REUSEPORT or SO_REUSEADDR
			 * socket options set.  This heuristic avoids searching
			 * through all pcbs in the common case of a non-shared
			 * port.  It assumes that an application will never
			 * clear these options after setting them.
			 */
			if (reuse_sock == 0 || ((m = n) == NULL))
				break;

			/*
			 * Expect 32-bit aligned data pointer on strict-align
			 * platforms.
			 */
			MBUF_STRICT_DATA_ALIGNMENT_CHECK_32(m);

			/*
			 * Recompute IP and UDP header pointers for new mbuf
			 */
			ip6 = mtod(m, struct ip6_hdr *);
			uh = (struct udphdr *)(void *)((caddr_t)ip6 + off);
		}
		lck_rw_done(pcbinfo->ipi_lock);

		if (mcast_delivered == 0) {
			/*
			 * No matching pcb found; discard datagram.
			 * (No need to send an ICMP Port Unreachable
			 * for a broadcast or multicast datgram.)
			 */
			udpstat.udps_noport++;
			udpstat.udps_noportmcast++;
			IF_UDP_STATINC(ifp, port_unreach);
			goto bad;
		}

		if (reuse_sock != 0)	/* free the extra copy of mbuf */
			m_freem(m);
		return (IPPROTO_DONE);
	}
	/*
	 * Locate pcb for datagram.
	 */
	in6p = in6_pcblookup_hash(&udbinfo, &ip6->ip6_src, uh->uh_sport,
	    &ip6->ip6_dst, uh->uh_dport, 1, m->m_pkthdr.rcvif);
	if (in6p == NULL) {
		IF_UDP_STATINC(ifp, port_unreach);

		if (udp_log_in_vain) {
			char buf[INET6_ADDRSTRLEN];

			strlcpy(buf, ip6_sprintf(&ip6->ip6_dst), sizeof (buf));
			if (udp_log_in_vain < 3) {
				log(LOG_INFO, "Connection attempt to UDP "
				    "%s:%d from %s:%d\n", buf,
				    ntohs(uh->uh_dport),
				    ip6_sprintf(&ip6->ip6_src),
				    ntohs(uh->uh_sport));
			} else if (!(m->m_flags & (M_BCAST | M_MCAST)) &&
			    !IN6_ARE_ADDR_EQUAL(&ip6->ip6_dst, &ip6->ip6_src)) {
				log_in_vain_log((LOG_INFO, "Connection attempt "
				    "to UDP %s:%d from %s:%d\n", buf,
				    ntohs(uh->uh_dport),
				    ip6_sprintf(&ip6->ip6_src),
				    ntohs(uh->uh_sport)));
			}
		}
		udpstat.udps_noport++;
		if (m->m_flags & M_MCAST) {
			printf("UDP6: M_MCAST is set in a unicast packet.\n");
			udpstat.udps_noportmcast++;
			IF_UDP_STATINC(ifp, badmcast);
			goto bad;
		}
		icmp6_error(m, ICMP6_DST_UNREACH, ICMP6_DST_UNREACH_NOPORT, 0);
		return (IPPROTO_DONE);
	}
#if IPSEC
	/*
	 * Check AH/ESP integrity.
	 */
	if (ipsec_bypass == 0) {
		if (ipsec6_in_reject_so(m, in6p->in6p_socket)) {
			IPSEC_STAT_INCREMENT(ipsec6stat.in_polvio);
			in_pcb_checkstate(in6p, WNT_RELEASE, 0);
			IF_UDP_STATINC(ifp, badipsec);
			goto bad;
		}
	}
#endif /* IPSEC */

	/*
	 * Construct sockaddr format source address.
	 * Stuff source address and datagram in user buffer.
	 */
	udp_lock(in6p->in6p_socket, 1, 0);

	if (in_pcb_checkstate(in6p, WNT_RELEASE, 1) == WNT_STOPUSING) {
		udp_unlock(in6p->in6p_socket, 1, 0);
		IF_UDP_STATINC(ifp, cleanup);
		goto bad;
	}

	init_sin6(&udp_in6, m); /* general init */
	udp_in6.sin6_port = uh->uh_sport;
	if ((in6p->in6p_flags & INP_CONTROLOPTS) != 0 ||
	    (in6p->in6p_socket->so_options & SO_TIMESTAMP) != 0 ||
	    (in6p->in6p_socket->so_options & SO_TIMESTAMP_MONOTONIC) != 0) {
		ret = ip6_savecontrol(in6p, m, &opts);
		if (ret != 0) {
			udp_unlock(in6p->in6p_socket, 1, 0);
			goto bad;
		}
	}
	m_adj(m, off + sizeof (struct udphdr));
	if (nstat_collect) {
		INP_ADD_STAT(in6p, cell, wifi, rxpackets, 1);
		INP_ADD_STAT(in6p, cell, wifi, rxbytes, m->m_pkthdr.len);
	}
	so_recv_data_stat(in6p->in6p_socket, m, 0);
	if (sbappendaddr(&in6p->in6p_socket->so_rcv,
	    (struct sockaddr *)&udp_in6, m, opts, NULL) == 0) {
		m = NULL;
		opts = NULL;
		udpstat.udps_fullsock++;
		udp_unlock(in6p->in6p_socket, 1, 0);
		goto bad;
	}
	sorwakeup(in6p->in6p_socket);
	udp_unlock(in6p->in6p_socket, 1, 0);
	return (IPPROTO_DONE);
bad:
	if (m != NULL)
		m_freem(m);
	if (opts != NULL)
		m_freem(opts);
	return (IPPROTO_DONE);
}

void
udp6_ctlinput(int cmd, struct sockaddr *sa, void *d)
{
	struct udphdr uh;
	struct ip6_hdr *ip6;
	struct mbuf *m;
	int off = 0;
	struct ip6ctlparam *ip6cp = NULL;
	const struct sockaddr_in6 *sa6_src = NULL;
	void (*notify)(struct inpcb *, int) = udp_notify;
	struct udp_portonly {
		u_int16_t uh_sport;
		u_int16_t uh_dport;
	} *uhp;

	if (sa->sa_family != AF_INET6 ||
	    sa->sa_len != sizeof (struct sockaddr_in6))
		return;

	if ((unsigned)cmd >= PRC_NCMDS)
		return;
	if (PRC_IS_REDIRECT(cmd))
		notify = in6_rtchange, d = NULL;
	else if (cmd == PRC_HOSTDEAD)
		d = NULL;
	else if (inet6ctlerrmap[cmd] == 0)
		return;

	/* if the parameter is from icmp6, decode it. */
	if (d != NULL) {
		ip6cp = (struct ip6ctlparam *)d;
		m = ip6cp->ip6c_m;
		ip6 = ip6cp->ip6c_ip6;
		off = ip6cp->ip6c_off;
		sa6_src = ip6cp->ip6c_src;
	} else {
		m = NULL;
		ip6 = NULL;
		sa6_src = &sa6_any;
	}

	if (ip6 != NULL) {
		/*
		 * XXX: We assume that when IPV6 is non NULL,
		 * M and OFF are valid.
		 */

		/* check if we can safely examine src and dst ports */
		if (m->m_pkthdr.len < off + sizeof (*uhp))
			return;

		bzero(&uh, sizeof (uh));
		m_copydata(m, off, sizeof (*uhp), (caddr_t)&uh);

		(void) in6_pcbnotify(&udbinfo, sa, uh.uh_dport,
		    (struct sockaddr*)ip6cp->ip6c_src, uh.uh_sport,
		    cmd, NULL, notify);
	} else {
		(void) in6_pcbnotify(&udbinfo, sa, 0,
		    (struct sockaddr *)&sa6_src, 0, cmd, NULL, notify);
	}
}

static int
udp6_abort(struct socket *so)
{
	struct inpcb *inp;

	inp = sotoinpcb(so);
	if (inp == NULL) {
		panic("%s: so=%p null inp\n", __func__, so);
		/* NOTREACHED */
	}
	soisdisconnected(so);
	in6_pcbdetach(inp);
	return (0);
}

static int
udp6_attach(struct socket *so, int proto, struct proc *p)
{
#pragma unused(proto)
	struct inpcb *inp;
	int error;

	inp = sotoinpcb(so);
	if (inp != NULL)
		return (EINVAL);

	error = in_pcballoc(so, &udbinfo, p);
	if (error)
		return (error);

	if (so->so_snd.sb_hiwat == 0 || so->so_rcv.sb_hiwat == 0) {
		error = soreserve(so, udp_sendspace, udp_recvspace);
		if (error)
			return (error);
	}
	inp = (struct inpcb *)so->so_pcb;
	inp->inp_vflag |= INP_IPV6;
	if (ip6_mapped_addr_on)
		inp->inp_vflag |= INP_IPV4;
	inp->in6p_hops = -1;	/* use kernel default */
	inp->in6p_cksum = -1;	/* just to be sure */
	/*
	 * XXX: ugly!!
	 * IPv4 TTL initialization is necessary for an IPv6 socket as well,
	 * because the socket may be bound to an IPv6 wildcard address,
	 * which may match an IPv4-mapped IPv6 address.
	 */
	inp->inp_ip_ttl = ip_defttl;
	if (nstat_collect)
		nstat_udp_new_pcb(inp);
	return (0);
}

static int
udp6_bind(struct socket *so, struct sockaddr *nam, struct proc *p)
{
	struct inpcb *inp;
	int error;

	inp = sotoinpcb(so);
	if (inp == NULL || (inp->inp_flags2 & INP2_WANT_FLOW_DIVERT))
		return (inp == NULL ? EINVAL : EPROTOTYPE);

	inp->inp_vflag &= ~INP_IPV4;
	inp->inp_vflag |= INP_IPV6;
	if ((inp->inp_flags & IN6P_IPV6_V6ONLY) == 0) {
		struct sockaddr_in6 *sin6_p;

		sin6_p = (struct sockaddr_in6 *)(void *)nam;

		if (IN6_IS_ADDR_UNSPECIFIED(&sin6_p->sin6_addr)) {
			inp->inp_vflag |= INP_IPV4;
		} else if (IN6_IS_ADDR_V4MAPPED(&sin6_p->sin6_addr)) {
			struct sockaddr_in sin;

			in6_sin6_2_sin(&sin, sin6_p);
			inp->inp_vflag |= INP_IPV4;
			inp->inp_vflag &= ~INP_IPV6;
			error = in_pcbbind(inp, (struct sockaddr *)&sin, p);
			return (error);
		}
	}

	error = in6_pcbbind(inp, nam, p);
	return (error);
}

int
udp6_connect(struct socket *so, struct sockaddr *nam, struct proc *p)
{
	struct inpcb *inp;
	int error;

	inp = sotoinpcb(so);
	if (inp == NULL || (inp->inp_flags2 & INP2_WANT_FLOW_DIVERT))
		return (inp == NULL ? EINVAL : EPROTOTYPE);

	if ((inp->inp_flags & IN6P_IPV6_V6ONLY) == 0) {
		struct sockaddr_in6 *sin6_p;

		sin6_p = (struct sockaddr_in6 *)(void *)nam;
		if (IN6_IS_ADDR_V4MAPPED(&sin6_p->sin6_addr)) {
			struct sockaddr_in sin;

			if (inp->inp_faddr.s_addr != INADDR_ANY)
				return (EISCONN);
			in6_sin6_2_sin(&sin, sin6_p);
			error = in_pcbconnect(inp, (struct sockaddr *)&sin,
			    p, IFSCOPE_NONE, NULL);
			if (error == 0) {
				inp->inp_vflag |= INP_IPV4;
				inp->inp_vflag &= ~INP_IPV6;
				soisconnected(so);
			}
			return (error);
		}
	}

	if (!IN6_IS_ADDR_UNSPECIFIED(&inp->in6p_faddr))
		return (EISCONN);
	error = in6_pcbconnect(inp, nam, p);
	if (error == 0) {
		/* should be non mapped addr */
		if (ip6_mapped_addr_on ||
		    (inp->inp_flags & IN6P_IPV6_V6ONLY) == 0) {
			inp->inp_vflag &= ~INP_IPV4;
			inp->inp_vflag |= INP_IPV6;
		}
		soisconnected(so);
		if (inp->inp_flowhash == 0)
			inp->inp_flowhash = inp_calc_flowhash(inp);
		/* update flowinfo - RFC 6437 */
		if (inp->inp_flow == 0 &&
		    inp->in6p_flags & IN6P_AUTOFLOWLABEL) {
			inp->inp_flow &= ~IPV6_FLOWLABEL_MASK;
			inp->inp_flow |=
			    (htonl(inp->inp_flowhash) & IPV6_FLOWLABEL_MASK);
		}
	}
	return (error);
}

static int
udp6_connectx(struct socket *so, struct sockaddr_list **src_sl,
    struct sockaddr_list **dst_sl, struct proc *p, uint32_t ifscope,
    associd_t aid, connid_t *pcid, uint32_t flags, void *arg,
    uint32_t arglen)
{
	return (udp_connectx_common(so, AF_INET6, src_sl, dst_sl,
	    p, ifscope, aid, pcid, flags, arg, arglen));
}

static int
udp6_detach(struct socket *so)
{
	struct inpcb *inp;

	inp = sotoinpcb(so);
	if (inp == NULL)
		return (EINVAL);
	in6_pcbdetach(inp);
	return (0);
}

static int
udp6_disconnect(struct socket *so)
{
	struct inpcb *inp;

	inp = sotoinpcb(so);
	if (inp == NULL || (inp->inp_flags2 & INP2_WANT_FLOW_DIVERT))
		return (inp == NULL ? EINVAL : EPROTOTYPE);

	if (inp->inp_vflag & INP_IPV4) {
		struct pr_usrreqs *pru;

		pru = ip_protox[IPPROTO_UDP]->pr_usrreqs;
		return ((*pru->pru_disconnect)(so));
	}

	if (IN6_IS_ADDR_UNSPECIFIED(&inp->in6p_faddr))
		return (ENOTCONN);

	in6_pcbdisconnect(inp);

	/* reset flow-controlled state, just in case */
	inp_reset_fc_state(inp);

	inp->in6p_laddr = in6addr_any;
	inp->in6p_last_outifp = NULL;
	so->so_state &= ~SS_ISCONNECTED;		/* XXX */
	return (0);
}

static int
udp6_disconnectx(struct socket *so, associd_t aid, connid_t cid)
{
#pragma unused(cid)
	if (aid != ASSOCID_ANY && aid != ASSOCID_ALL)
		return (EINVAL);

	return (udp6_disconnect(so));
}

static int
udp6_send(struct socket *so, int flags, struct mbuf *m, struct sockaddr *addr,
    struct mbuf *control, struct proc *p)
{
	struct inpcb *inp;
	int error = 0;

	inp = sotoinpcb(so);
	if (inp == NULL || (inp->inp_flags2 & INP2_WANT_FLOW_DIVERT)) {
		error = (inp == NULL ? EINVAL : EPROTOTYPE);
		goto bad;
	}

	if (addr != NULL) {
		if (addr->sa_len != sizeof (struct sockaddr_in6)) {
			error = EINVAL;
			goto bad;
		}
		if (addr->sa_family != AF_INET6) {
			error = EAFNOSUPPORT;
			goto bad;
		}
	}

	if (ip6_mapped_addr_on || (inp->inp_flags & IN6P_IPV6_V6ONLY) == 0) {
		int hasv4addr;
		struct sockaddr_in6 *sin6 = NULL;

		if (addr == NULL) {
			hasv4addr = (inp->inp_vflag & INP_IPV4);
		} else {
			sin6 = (struct sockaddr_in6 *)(void *)addr;
			hasv4addr =
			    IN6_IS_ADDR_V4MAPPED(&sin6->sin6_addr) ? 1 : 0;
		}
		if (hasv4addr) {
			struct pr_usrreqs *pru;

			if (sin6 != NULL)
				in6_sin6_2_sin_in_sock(addr);
			pru = ip_protox[IPPROTO_UDP]->pr_usrreqs;
			error = ((*pru->pru_send)(so, flags, m, addr,
			    control, p));
			/* addr will just be freed in sendit(). */
			return (error);
		}
	}
	return (udp6_output(inp, m, addr, control, p));

bad:
	VERIFY(error != 0);

	if (m != NULL)
		m_freem(m);
	if (control != NULL)
		m_freem(control);

	return (error);
}

/*
 * Checksum extended UDP header and data.
 */
static int
udp6_input_checksum(struct mbuf *m, struct udphdr *uh, int off, int ulen)
{
	struct ifnet *ifp = m->m_pkthdr.rcvif;
	struct ip6_hdr *ip6 = mtod(m, struct ip6_hdr *);

	if (uh->uh_sum == 0) {
		/* UDP/IPv6 checksum is mandatory (RFC2460) */
		udpstat.udps_nosum++;
		goto badsum;
	}

	if ((hwcksum_rx || (ifp->if_flags & IFF_LOOPBACK) ||
	    (m->m_pkthdr.pkt_flags & PKTF_LOOP)) &&
	    (m->m_pkthdr.csum_flags & CSUM_DATA_VALID)) {
		if (m->m_pkthdr.csum_flags & CSUM_PSEUDO_HDR) {
			uh->uh_sum = m->m_pkthdr.csum_rx_val;
		} else {
			uint16_t sum = m->m_pkthdr.csum_rx_val;
			uint16_t start = m->m_pkthdr.csum_rx_start;

			/*
			 * Perform 1's complement adjustment of octets
			 * that got included/excluded in the hardware-
			 * calculated checksum value.
			 */
			if ((m->m_pkthdr.csum_flags & CSUM_PARTIAL) &&
			    start != off) {
				uint16_t s, d;

				if (IN6_IS_SCOPE_EMBED(&ip6->ip6_src)) {
					s = ip6->ip6_src.s6_addr16[1];
					ip6->ip6_src.s6_addr16[1] = 0 ;
				}
				if (IN6_IS_SCOPE_EMBED(&ip6->ip6_dst)) {
					d = ip6->ip6_dst.s6_addr16[1];
					ip6->ip6_dst.s6_addr16[1] = 0;
				}

				/* callee folds in sum */
				sum = m_adj_sum16(m, start, off, sum);

				if (IN6_IS_SCOPE_EMBED(&ip6->ip6_src))
					ip6->ip6_src.s6_addr16[1] = s;
				if (IN6_IS_SCOPE_EMBED(&ip6->ip6_dst))
					ip6->ip6_dst.s6_addr16[1] = d;
			}

			uh->uh_sum = in6_pseudo(&ip6->ip6_src, &ip6->ip6_dst,
			    sum + htonl(ulen + IPPROTO_UDP));
		}
		uh->uh_sum ^= 0xffff;
	} else {
		udp_in6_cksum_stats(ulen);
		uh->uh_sum = in6_cksum(m, IPPROTO_UDP, off, ulen);
	}

	if (uh->uh_sum != 0) {
badsum:
		udpstat.udps_badsum++;
		IF_UDP_STATINC(ifp, badchksum);
		return (-1);
	}

	return (0);
}