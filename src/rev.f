rev([],[]).
rev([1],[1]).
rev([2],[2]).
rev([3],[3]).
rev([4],[4]).
rev([1,2],[2,1]).
rev([1,3],[3,1]).
rev([1,4],[4,1]).
rev([2,2],[2,2]).
rev([2,3],[3,2]).
rev([2,4],[4,2]).
rev([0,1,2],[2,1,0]).
rev([1,2,3],[3,2,1]).
% rev([2,4,3],[3,4,2]).
% rev([4,1,2],[2,1,4]).
% rev([1,2,3,4],[4,3,2,1]).
% rev([2,1,3,4],[4,3,1,2]).
% rev([A|B],[C|D]) :- rev(B,E), p(E,A,C,D)
% p([],1,1,[])
% p([],2,2,[])
% p([],3,3,[])
% p([],4,4,[])
% p([2],1,2,[1])
% p([3],1,3,[1])
% p([4],1,4,[1])
% p([2],2,2,[2])
% p([3],2,3,[2])
% p([4],2,4,[2])
% p([2,1],0,2,[1,0])
% p([3,2],1,3,[2,1])
