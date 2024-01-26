@lycyxyyyy3yx("")
@lyyxBBBBBBBB("")
permit(
  principal is A::a in A::a::"",
  action in [A::Action::"6"],
  resource is A::a in A::a::""
) when {
  true && ((if (action has "\0") then A::Action::"6" else A::a::"") has "6")
};
