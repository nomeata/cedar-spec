@k66666666("")
permit(
  principal == B::a::"",
  action == B::Action::"action",
  resource == B::a::""
) when {
  true && ((if (action has "k6sssssss") then (if true then action else resource) else B::a::"") has "k6sssssss")
};
