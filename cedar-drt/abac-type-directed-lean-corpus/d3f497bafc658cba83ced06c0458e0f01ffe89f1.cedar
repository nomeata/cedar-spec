@B("6")
@B0ssssssssssF("3")
@Bsss("6[")
@M("6\u{1}\u{11}66,?6\06666666333")
@m("")
@r("")
permit(
  principal in l::"6\u{1}\u{11}66",
  action in [Action::""],
  resource is l in l::"6\u{1}\u{11}66"
) when {
  (true && ((ip(principal["r"])).isIpv4())) && ((ip(principal["r"])).isIpv4())
};
