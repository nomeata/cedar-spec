permit(
  principal == r::r::r::r::r::AhhdZ::r::wS::"",
  action == r::r::r::r::r::AhhdZ::r::Action::"action",
  resource == r::r::r::r::r::AhhdZ::r::wS::""
) when {
  (true && (!(r::r::r::r::r::AhhdZ::r::Action::"action".containsAll(if principal then principal else principal)))) && principal
};
