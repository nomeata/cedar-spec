@Bsss("6\0\0/")
@Bssss100l32303("")
@E("653")
@I("[\u{7}")
@m("\u{1}\0\0/")
@psscdssggl3("\u{2}")
@r("")
@r03("")
permit(
  principal,
  action in [Action::""],
  resource
) when {
  ((true && ((if ((ip("200.248.255.54")).isIpv4()) then [11430820774659, 8247620832361185285, 217020518520284515] else []) == [])) && true) && true
};
